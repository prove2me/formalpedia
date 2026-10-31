-- Prove2me | Theorems.Thm_CongruencyTU_lemma_21
-- name    : CongruencyTU.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:52.593148+00:00
-- url     : https://prove2.me/theorems/12a4c53b-d096-4b5b-99bf-85ef1c07242c
-- title:
--   Lemma 21: for prime m and |R| ≥ m − 2 one linear sub-pattern of the narrowed pattern suffices
-- statement:
--   Let $\pi:\Pi_{\mathrm{narrowed}}\to2^{\{0,\dots,m-1\}}$ be a narrowed pattern associated to a feasible R-CCTUF problem of form (1) with prime modulus $m$ and $|R|\ge m-2$. One can determine in strongly polynomial time a linear sub-pattern $\tilde\pi$ of $\pi$ such that one of the following holds:
--
--   1. there is $(\alpha,\beta)\in\Pi_{\mathrm{narrowed}}$ with $|\pi(\alpha,\beta)|=1$ such that for every $x_A$ solving the relaxation of the A-problem for $(\alpha,\beta)$ there is an $x_B$ solving the relaxation of the B-problem for $(\alpha,\beta)$ with $(x_A,x_B)$ feasible for the R-CCTUF problem;
--   2. there is a feasible solution for some $(\alpha,\beta)\in\Pi_{\mathrm{narrowed}}$ with $|\pi(\alpha,\beta)|\ge2$;
--   3. there is a feasible solution $(x_A,x_B)$ for some $(\alpha,\beta)\in\mathrm{dom}(\tilde\pi)$ with $\tilde\pi(\alpha,\beta)=\{\gamma_B^\top x_B\}$.
--
--   This is the step that lets the recursion of Theorem 22 make progress when the pattern is not linear.
--
--   **Formalization Note** The algorithm reads the problem, the bounds and the narrowed pattern as a finite table, and outputs the domain bounds $\ell',u'$ and $r_0,r_1,r_2$ of $\tilde\pi(\alpha,\beta)=\{(r_0+r_1\alpha+r_2\beta)\bmod m\}$.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "an R-CCTUF problem of the form given in (1)" → a Form1 whose two 3-sum summands (A e e; h⊤ 0 1) and (0 1 f⊤; g g B) are totally unimodular (zero vectors for 1- and 2-sums), with m > 0 and R ⊆ {0, …, m − 1}; reason: form (1) is introduced for case (iii) of Theorem 14, a decomposition into totally unimodular summands (p.9); the 3-sum of TU summands is TU (p.8)
--   - reading: "π an associated narrowed pattern" / "the above setup": the narrowed pattern for the bounds ℓᵢ, uᵢ of Lemma 16 → any bounds ℓ, u with Lemma 16's guarantee (uᵢ − ℓᵢ ≤ m − |R|, and a solution within the bounds if (1) is feasible), and the narrowed pattern defined from them; reason: Lemma 16 specifies its bounds only by this guarantee; the narrowed pattern depends on the choice (p.10)
--   - encoding: π given; "determine a linear sub-pattern π̃" → input enc(problem) ++ ℓ ++ u ++ patternTable (the narrowed pattern as a finite table); output ℓ' ++ u' ++ [r₀, r₁, r₂] describing π̃(α, β) = {(r₀ + r₁α + r₂β) mod m} on the hexagon of ℓ', u'; reason: every linear sub-pattern has this form (Definitions 17 and 61); the table is π itself
--   - reading: π̃(α, β) = {γ_B⊤x_B} → π̃(α, β) = {γ_B⊤x_B mod m}; reason: pattern values are residues in {0, …, m − 1}
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, pp.12–13 (PDF pp.13–14), Lemma 21

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Pattern

open Matrix

namespace CongruencyTU

/-- **Lemma 21** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), pp.12–13, PDF pp.13–14): "Let π : Π_narrowed → 2^{0,…,m−1} be a narrowed
pattern associated to a feasible R-CCTUF problem of the form in (1) with prime modulus m and
|R| ≥ m − 2. Then, we can in strongly polynomial time determine a linear sub-pattern π̃ of π such
that one of the following holds: (i) There are (α, β) ∈ Π_narrowed with |π(α, β)| = 1 so that for
any x_A solving the relaxation of the A-problem with respect to (α, β), there is an x_B solving the
relaxation of the B-problem such that the combination (x_A, x_B) is feasible for the R-CCTUF
problem. (ii) There is a feasible solution for some pair (α, β) ∈ Π_narrowed with |π(α, β)| ≥ 2.
(iii) There is a feasible solution (x_A, x_B) for some pair (α, β) ∈ dom(π̃) such that
π̃(α, β) = {γ_B⊤x_B}."

One deterministic strongly polynomial program that, on `enc(problem) ++ ℓ ++ u ++ table(π)`,
outputs bounds `ℓ', u'` and residues `r₀, r₁, r₂` describing the linear sub-pattern
`π̃(α, β) = {(r₀ + r₁α + r₂β) mod m}` on the domain `{ℓ'₀ ≤ α + β ≤ u'₀, ℓ'₁ ≤ α ≤ u'₁,
ℓ'₂ ≤ β ≤ u'₂}`, such that (i), (ii) or (iii) holds.

**Formalization Note.** The narrowed pattern is that of the bounds `ℓ, u` of Lemma 16
(`Lemma16Bounds`), given to the program as the finite table `patternTable`. A linear sub-pattern
(Definitions 17 and 61) has a hexagonal domain inside `Π_narrowed` and one residue
`r(α, β) ∈ π(α, β)` per point with `r(α, β) ≡ r₀ + r₁α + r₂β (mod m)`; every such sub-pattern is
`linPat m r₀ r₁ r₂` on its domain. In (iii), `{γ_B⊤x_B}` is read modulo `m`. -/
theorem lemma_21 :
    ∃ (P : Program) (p q : Polynomial ℕ), ∀ (F : Form1) (ℓ u : Fin 3 → ℤ),
      F.Valid → F.Feasible → F.m.Prime → F.m - 2 ≤ F.R.card → F.Lemma16Bounds ℓ u →
      DetRunOK P (F.enc ++ encVec ℓ ++ encVec u ++ F.patternTable ℓ u) p q ∧
      ∃ (ℓ' u' : Fin 3 → ℤ) (r₀ r₁ r₂ : ℤ),
        detOut P (F.enc ++ encVec ℓ ++ encVec u ++ F.patternTable ℓ u) p =
          encVec ℓ' ++ encVec u' ++ [r₀, r₁, r₂] ∧
        F.IsSubPattern ℓ u (hexagon ℓ' u') (linPat F.m r₀ r₁ r₂) ∧
        ((∃ α β : ℤ, (α, β) ∈ F.narrowed ℓ u ∧ (F.pattern (α, β)).card = 1 ∧
            ∀ xA, F.RelA α β xA → ∃ xB, F.RelB α β xB ∧ F.IsSol xA xB) ∨
         (∃ xA xB, F.IsSol xA xB ∧ (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA) ∈ F.narrowed ℓ u ∧
            2 ≤ (F.pattern (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA)).card) ∨
         (∃ xA xB, F.IsSol xA xB ∧ (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA) ∈ hexagon ℓ' u' ∧
            linPat F.m r₀ r₁ r₂ (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA) =
              {((F.γB ⬝ᵥ xB) % (F.m : ℤ)).toNat})) := by sorry

end CongruencyTU
