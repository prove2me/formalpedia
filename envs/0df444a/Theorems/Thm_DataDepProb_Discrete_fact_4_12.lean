-- Prove2me | Theorems.Thm_DataDepProb_Discrete_fact_4_12
-- name    : DataDepProb.Discrete.fact_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:49.469733+00:00
-- url     : https://prove2.me/theorems/26e312b1-23c3-4b98-9315-5afee3dccc20
-- title:
--   Fact 4.12 — the KL projection onto $\tilde\Delta_d$ is $\max\{1/(2d),cz(x)\}$ and is computable in $O(d)$ operations
-- statement:
--   Let $z\in\Delta_d$ have positive coordinates and $\tilde\Delta_d=\{q\in\Delta_d:q(x)\ge1/(2d)\ \forall x\}$. The minimizer of $\mathrm{KL}(q\|z)$ over $q\in\tilde\Delta_d$ has coordinates
--   $$q(x)=\max\Big\{\frac1{2d},\,c\,z(x)\Big\},\qquad c>0,\qquad \sum_x q(x)=1 .$$
--   This projection can be computed in $O(d)$ operations: there are one admissible oracle-free program and one constant $C$ such that, for every $d$ and every such $z$, the run with $d$ in pointer register $0$ and $z$ in real memory cells $0,\dots,d-1$ halts within $C\cdot d$ steps and leaves the minimizer in real memory cells $0,\dots,d-1$.
--
--   It is the $\lambda=0$ case of the penalized projection (Proposition C.1) and the projection step of the simple estimator.
--
--   Differences from the source:
--   - reading: "The minimizer … has coordinates …" → a minimizer exists, and every minimizer has that form for some $c>0$ (the normalization is part of membership in $\tilde\Delta_d$); reason: "the minimizer" presupposes existence.
--   - reading: "can be computed in $O(d)$ operations" → ∃ program (`Admissible`, `OracleFree`) ∃ $C>0$ ∀ $d$, $z$: `HaltsWithin … (C * d)`, and the output vector lies in $\tilde\Delta_d$ and minimizes $\mathrm{KL}(\cdot\|z)$ there; reason: the machine reading of the mission; the program and constant are fixed before $d$.
--   - encoding: $[d]$ → `Fin d`; input $d$ in pointer register $0$, $z$ in real cells $0..d-1$, output in real cells $0..d-1$; reason: input/output convention.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 11, Fact 4.12

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_Machine

namespace DataDepProb.Discrete

/-- Fact 4.12 (computing KL projection, p. 11). Let `z ∈ ∆_d` have positive coordinates and
`∆̃_d = {q ∈ ∆_d : q(x) ≥ 1/(2d)}`. The minimizer of `KL(q‖z)` over `∆̃_d` exists, and every
minimizer has coordinates `q(x) = max{1/(2d), c z(x)}` for some `c > 0` (with `∑_x q(x) = 1`).
The projection can be computed in `O(d)` operations: one fixed deterministic oracle-free program
with rational literals and one constant `C`, such that for every `d` and every such `z`, the run on
input (`d` in pointer register `0`, `z(0), …, z(d − 1)` in real memory cells `0, …, d − 1`) halts
after at most `C·d` steps with the minimizer in real memory cells `0, …, d − 1`. -/
theorem fact_4_12 :
    (∀ (d : ℕ) (z : Fin d → ℝ), z ∈ simplex d → (∀ x, 0 < z x) →
      (∃ q ∈ truncSimplex d, IsMinOn (fun q => kl q z) (truncSimplex d) q) ∧
      ∀ q ∈ truncSimplex d, IsMinOn (fun q => kl q z) (truncSimplex d) q →
        ∃ c : ℝ, 0 < c ∧ ∀ x, q x = max (1 / (2 * (d : ℝ))) (c * z x)) ∧
    ∃ P : Program, Admissible P ∧ OracleFree P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (z : Fin d → ℝ), z ∈ simplex d → (∀ x, 0 < z x) →
        HaltsWithin P detG zeroTape (initState [(d : ℤ)] [] (List.ofFn z)) (C * d) ∧
        outVec P detG zeroTape (initState [(d : ℤ)] [] (List.ofFn z)) d ∈ truncSimplex d ∧
        IsMinOn (fun q => kl q z) (truncSimplex d)
          (outVec P detG zeroTape (initState [(d : ℤ)] [] (List.ofFn z)) d) := by sorry

end DataDepProb.Discrete
