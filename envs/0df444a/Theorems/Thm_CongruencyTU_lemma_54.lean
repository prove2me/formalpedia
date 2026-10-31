-- Prove2me | Theorems.Thm_CongruencyTU_lemma_54
-- name    : CongruencyTU.lemma_54
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:12.759935+00:00
-- url     : https://prove2.me/theorems/d8213188-4cb0-400c-96c5-317aa5ba82ed
-- title:
--   Lemma 54: the narrowed domain is a hexagon without holes, computable in strongly polynomial time
-- statement:
--   Consider an R-CCTUF problem of form (1), bounds $\ell_i,u_i$ ($i\in\{0,1,2\}$) as in Lemma 16, and
--   $$\Pi_{\mathrm{narrowed}}=\Pi\cap\{(\alpha,\beta)\in\mathbb Z^2:\ell_0\le\alpha+\beta\le u_0,\ \ell_1\le\alpha\le u_1,\ \ell_2\le\beta\le u_2\}.$$
--   One can determine in strongly polynomial time $\ell'_i,u'_i$ with $u'_i-\ell'_i\le m-|R|$ such that
--   $$\Pi_{\mathrm{narrowed}}=\{(\alpha,\beta)\in\mathbb Z^2:\ell'_0\le\alpha+\beta\le u'_0,\ \ell'_1\le\alpha\le u'_1,\ \ell'_2\le\beta\le u'_2\}.$$
--
--   The point is that every pair satisfying the new bounds lies in $\Pi$: the domain of the narrowed pattern has no holes, which is what makes linear patterns and Theorem 18 usable.
--
--   **Formalization Note** One deterministic program reads the problem and $\ell,u$ and outputs $\ell',u'$.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "an R-CCTUF problem of the form given in (1)" → a Form1 whose two 3-sum summands (A e e; h⊤ 0 1) and (0 1 f⊤; g g B) are totally unimodular (zero vectors for 1- and 2-sums), with m > 0 and R ⊆ {0, …, m − 1}; reason: form (1) is introduced for case (iii) of Theorem 14, a decomposition into totally unimodular summands (p.9); the 3-sum of TU summands is TU (p.8)
--   - reading: "π an associated narrowed pattern" / "the above setup": the narrowed pattern for the bounds ℓᵢ, uᵢ of Lemma 16 → any bounds ℓ, u with Lemma 16's guarantee (uᵢ − ℓᵢ ≤ m − |R|, and a solution within the bounds if (1) is feasible), and the narrowed pattern defined from them; reason: Lemma 16 specifies its bounds only by this guarantee; the narrowed pattern depends on the choice (p.10)
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.37 (PDF p.38), Lemma 54; setup pp.36–37, (21)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Pattern

namespace CongruencyTU

/-- **Lemma 54** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.37, PDF p.38): "In the above setup, we can in strongly polynomial time
determine ℓ'ᵢ, u'ᵢ for i ∈ {0, 1, 2} with u'ᵢ − ℓ'ᵢ ≤ m − |R| such that
Π_narrowed = {(α, β) ∈ ℤ² : ℓ'₀ ≤ α + β ≤ u'₀, ℓ'₁ ≤ α ≤ u'₁, ℓ'₂ ≤ β ≤ u'₂}."

The setup (pp.36–37): an R-CCTUF problem of form (1), the bounds `ℓᵢ, uᵢ` of Lemma 16 and
`Π_narrowed = Π ∩ {ℓ₀ ≤ α + β ≤ u₀, ℓ₁ ≤ α ≤ u₁, ℓ₂ ≤ β ≤ u₂}` (21). One deterministic strongly
polynomial program that, on `enc(problem) ++ ℓ ++ u`, outputs `ℓ' ++ u'` with these properties.

**Formalization Note.** The bounds of Lemma 16 enter as any `ℓ, u` with Lemma 16's guarantee
(`Lemma16Bounds`); index `0` is `α + β`, `1` is `α`, `2` is `β`. -/
theorem lemma_54 :
    ∃ (P : Program) (p q : Polynomial ℕ), ∀ (F : Form1) (ℓ u : Fin 3 → ℤ),
      F.Valid → F.Lemma16Bounds ℓ u →
      DetRunOK P (F.enc ++ encVec ℓ ++ encVec u) p q ∧
      ∃ ℓ' u' : Fin 3 → ℤ, detOut P (F.enc ++ encVec ℓ ++ encVec u) p = encVec ℓ' ++ encVec u' ∧
        (∀ i, u' i - ℓ' i ≤ (F.m : ℤ) - F.R.card) ∧
        F.narrowed ℓ u = hexagon ℓ' u' := by sorry

end CongruencyTU
