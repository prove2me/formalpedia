-- Prove2me | Theorems.Thm_AC02Frege_Supplement_theorem_3_14
-- name    : AC02Frege.Supplement.theorem_3_14
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:57:56.38737+00:00
-- url     : https://prove2.me/theorems/850571c6-b177-4fa6-8825-e1630330fcec
-- title:
--   Theorem 3.14 — Pang's degree–size relation for $\mathrm{Res}(\mathrm{PC}_r)$
-- statement:
--   Let $F$ be an unsatisfiable CNF on $n$ variables with no polynomial-calculus refutation over $\mathbb F_2$ of degree at most $D$, where
--   $$
--   \max\{32r,\ 8w(F)\}\le D\le n,
--   $$
--   and $w(F)$ is the width of $F$. Then every $S$-line syntactic $\mathrm{Res}(\mathrm{PC}_r)$ refutation of $F$ satisfies
--   $$
--   \log S\ \ge\ \frac{D}{128r}\Bigl(\frac{D}{16n}\Bigr)^{r}. \tag{16}
--   $$
--
--   This is Pang's theorem (Theorem 1.1 of the paper, after Pang 2026) over $\mathbb F_2$ with all constants explicit: a linear PC degree lower bound gives line lower bounds $\exp(\Omega(n))$ for constant $r$ and $\exp(n^{\Omega(1)})$ for $r$ a small constant multiple of $\log n$. The rest of the paper improves the decay $(D/16n)^r$ by a majority lift.
--
--   **Formalization Note** "Syntactic" means exactly the rules of Definition 2.6. The degree bound $r$ applies to the formal degree of every polynomial of every line.
--
--   Differences from the source:
--   - generalization: lines as disjunctions of equations, with weakening and contraction as rules → lines as finite sets of polynomials (RLine), contraction and reordering built in; reason: each line of a refutation in the paper's form maps to its set of polynomials, and every rule application maps to a rule application, so a paper refutation gives a set-based one with the same number of lines (and the same total size); the lower bound for set-based refutations specializes to the source
--   - encoding: "no PC refutation of degree at most D" → ¬ PCDerivable F D 1 (base definition: formal degree, Boolean axioms y_i² + y_i); reason: formal degrees are integers, so degree ≤ cn means degree ≤ ⌊cn⌋; same instances
--   - encoding: F an unsatisfiable CNF on n variables y_1, …, y_n; w(F) its width → F : LiftSAParity.CNF (Fin n) with ¬ Satisfiable F; width F (base, largest clause size); reason: same instances
--   - encoding: log; S the number of lines → Real.log (natural logarithm); S = π.length; reason: the proof of (14)/(16) uses the natural logarithm (it compares S·e^{−ηt}); same instances
--   - encoding: r a degree bound, for which D/(128r) is defined only when r ≥ 1 → r : ℕ with no r ≥ 1 hypothesis; at r = 0 Lean's D/0 = 0 makes (16) read 0 ≤ log S; reason: r = 0 is outside the source's statement; the Lean reading there is true (S ≥ 1) and every r ≥ 1 is the source's case
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem 3.14, p.19 (Theorem 1.1 restated, p.3); Definitions 2.4, 2.6, 2.7, pp.9–11

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_Supplement_ResPC

namespace AC02Frege.Supplement

open LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower
Bounds*, manuscript (sha256 88d149fa…), Theorem 3.14, p.19 (Pang's degree–size relation;
Theorem 1.1 restated): let `F` be an unsatisfiable CNF on `n` variables with no PC refutation of
degree at most `D`, where `max{32r, 8w(F)} ≤ D ≤ n`. Then every `S`-line syntactic `Res(PC_r)`
refutation of `F` satisfies `log S ≥ D/(128r) · (D/(16n))^r` (16).

**Formalization Note** "No PC refutation of degree at most `D`" is `¬ PCDerivable F D 1` (formal
degree, Boolean axioms; base definition). `Res(PC_r)` bounds the formal degree of every polynomial
of every line by `r`; `S` is the number of lines. `log` is the natural logarithm. No `r ≥ 1`
hypothesis is added: at `r = 0` Lean's `D/0 = 0` makes (16) read `0 ≤ log S`. -/
theorem theorem_3_14 {n : ℕ} (F : CNF (Fin n)) (D r : ℕ)
    (hunsat : ¬ Satisfiable F) (hdeg : ¬ AC02Frege.PCDerivable F D 1)
    (hr : 32 * r ≤ D) (hw : 8 * AC02Frege.width F ≤ D) (hDn : D ≤ n)
    (π : List (RLine (Fin n))) (hπ : IsResRefutation (r : ℕ∞) F π) :
    (D : ℝ) / (128 * r) * ((D : ℝ) / (16 * n)) ^ r ≤ Real.log π.length := by sorry

end AC02Frege.Supplement
