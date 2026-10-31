-- Prove2me | Theorems.Thm_CongruencyTU_theorem_18
-- name    : CongruencyTU.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:05.478285+00:00
-- url     : https://prove2.me/theorems/f748f077-aa0c-4a82-81ba-e7da04301868
-- title:
--   Theorem 18: a linear narrowed pattern reduces problem (1) to the R-CCTUF problem (3) in two extra variables
-- statement:
--   Consider an R-CCTUF problem of form (1) and an associated narrowed pattern $\pi$. If $\pi$ is linear, then (1) can be reduced to the R-CCTUF problem
--   $$\begin{aligned}Ax_A+ey_1&\le b_A,\qquad h^\top x_A-y_2=0,\\ \ell_0\le y_1+y_2&\le u_0,\quad \ell_1\le y_1\le u_1,\quad \ell_2\le y_2\le u_2,\\ \gamma_A^\top x_A+r_1y_1+r_2y_2&\in r_0+R\pmod m,\qquad x_A\in\mathbb Z^{n_A},\ y_1,y_2\in\mathbb Z,\end{aligned}\tag{3}$$
--   for suitable $\ell_i,u_i\in\mathbb Z$ with $u_i-\ell_i\le m-|R|$ and $r_0,r_1,r_2\in\{0,\dots,m-1\}$ that can be determined in strongly polynomial time. That is, (1) is feasible if and only if (3) is, and a solution of either problem can be transformed into a solution of the other in strongly polynomial time.
--
--   System (3) replaces $x_B$ by two variables standing for the scalar products; with Theorem 19 it reduces the number of variables.
--
--   **Formalization Note** Three deterministic programs: one computes $\ell',u',r_0,r_1,r_2$, the other two transform solutions in each direction. The statement includes that (3) is an R-CCTUF problem, i.e. its constraint matrix (equation and two-sided bounds written as pairs of inequalities) is totally unimodular.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "an R-CCTUF problem of the form given in (1)" → a Form1 whose two 3-sum summands (A e e; h⊤ 0 1) and (0 1 f⊤; g g B) are totally unimodular (zero vectors for 1- and 2-sums), with m > 0 and R ⊆ {0, …, m − 1}; reason: form (1) is introduced for case (iii) of Theorem 14, a decomposition into totally unimodular summands (p.9); the 3-sum of TU summands is TU (p.8)
--   - reading: "π an associated narrowed pattern" / "the above setup": the narrowed pattern for the bounds ℓᵢ, uᵢ of Lemma 16 → any bounds ℓ, u with Lemma 16's guarantee (uᵢ − ℓᵢ ≤ m − |R|, and a solution within the bounds if (1) is feasible), and the narrowed pattern defined from them; reason: Lemma 16 specifies its bounds only by this guarantee; the narrowed pattern depends on the choice (p.10)
--   - encoding: system (3) with an equation, two-sided bounds and "∈ r₀ + R (mod m)" → Form1.sys3: an R-CCTUF instance in (x_A, y₁, y₂) with the equation and each two-sided bound as two inequalities and target residues {(r₀ + r) mod m : r ∈ R}; reason: the same solution set; (3) is called an R-CCTUF problem, so its total unimodularity is part of the claim
--   - encoding: "a solution of one problem can be transformed into one for the other in strongly polynomial time" → programs Pf and Pb reading pack [enc(problem) ++ ℓ ++ u, solution]; reason: the transformations may read the instance and the bounds
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.11 (PDF p.12), Theorem 18, system (3)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Pattern

namespace CongruencyTU

/-- **Theorem 18** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.11, PDF p.12): "Consider an R-CCTUF problem of the form given in (1) and
let π an associated narrowed pattern. If π is linear, then (1) can be reduced to the R-CCTUF problem
[(3): A x_A + e y₁ ≤ b_A, h⊤x_A − y₂ = 0, ℓ₀ ≤ y₁ + y₂ ≤ u₀, ℓ₁ ≤ y₁ ≤ u₁, ℓ₂ ≤ y₂ ≤ u₂,
γ_A⊤x_A + r₁y₁ + r₂y₂ ∈ r₀ + R (mod m), x_A ∈ ℤ^{nA}, y₁, y₂ ∈ ℤ] for suitable
ℓ₀, u₀, ℓ₁, u₁, ℓ₂, u₂ ∈ ℤ with uᵢ − ℓᵢ ≤ m − |R| and r₀, r₁, r₂ ∈ {0, 1, …, m − 1} that can be
determined in strongly polynomial time. That is, the initial R-CCTUF problem is feasible if and only
if (3) is, and a solution of one problem can be transformed into one for the other in strongly
polynomial time."

Three deterministic strongly polynomial programs: `P` computes the parameters of (3) from
`enc(problem) ++ ℓ ++ u` (the bounds of Lemma 16 defining the narrowed pattern); `Pf` maps a solution
of (1) to one of (3); `Pb` maps a solution of (3) to one of (1). System (3) is an R-CCTUF problem: its
constraint matrix is totally unimodular.

**Formalization Note.** (3) is `Form1.sys3` (the equation and the two-sided bounds as pairs of
inequalities; `r₀ + R` as the residue set `{(r₀ + r) mod m}`). The transformation programs receive
`pack [enc(problem) ++ ℓ ++ u, solution]`. -/
theorem theorem_18 :
    ∃ (P Pf Pb : Program) (p q : Polynomial ℕ), ∀ (F : Form1) (ℓ u : Fin 3 → ℤ),
      F.Valid → F.Lemma16Bounds ℓ u → IsLinearOn F.m (F.narrowed ℓ u) F.pattern →
      DetRunOK P (F.enc ++ encVec ℓ ++ encVec u) p q ∧
      ∃ (ℓ' u' : Fin 3 → ℤ) (r₀ r₁ r₂ : ℤ),
        detOut P (F.enc ++ encVec ℓ ++ encVec u) p = encVec ℓ' ++ encVec u' ++ [r₀, r₁, r₂] ∧
        (∀ i, u' i - ℓ' i ≤ (F.m : ℤ) - F.R.card) ∧
        (0 ≤ r₀ ∧ r₀ < F.m) ∧ (0 ≤ r₁ ∧ r₁ < F.m) ∧ (0 ≤ r₂ ∧ r₂ < F.m) ∧
        (F.sys3 ℓ' u' r₀ r₁ r₂).Valid ∧
        (F.Feasible ↔ (F.sys3 ℓ' u' r₀ r₁ r₂).Feasible) ∧
        (∀ xA xB, F.IsSol xA xB →
          DetRunOK Pf (pack [F.enc ++ encVec ℓ ++ encVec u, encVec xA ++ encVec xB]) p q ∧
          ∃ y, (F.sys3 ℓ' u' r₀ r₁ r₂).IsSol y ∧
            detOut Pf (pack [F.enc ++ encVec ℓ ++ encVec u, encVec xA ++ encVec xB]) p =
              encVec y) ∧
        (∀ y, (F.sys3 ℓ' u' r₀ r₁ r₂).IsSol y →
          DetRunOK Pb (pack [F.enc ++ encVec ℓ ++ encVec u, encVec y]) p q ∧
          ∃ xA xB, F.IsSol xA xB ∧
            detOut Pb (pack [F.enc ++ encVec ℓ ++ encVec u, encVec y]) p =
              encVec xA ++ encVec xB) := by sorry

end CongruencyTU
