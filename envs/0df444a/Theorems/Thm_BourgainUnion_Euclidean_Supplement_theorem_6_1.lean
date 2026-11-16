-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_6_1
-- name    : BourgainUnion.Euclidean.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:02.531187+00:00
-- url     : https://prove2.me/theorems/1726dc6c-024e-4efd-ae29-305a722acea3
-- title:
--   Theorem 6.1 — unions of 1-strongly Euclidean sets with $e_{\max}\ge\frac12(\log_2k)^{1/4}$
-- statement:
--   For every integer $k\ge2$ there is a finite metric space $X=U_1\cup\dots\cup U_k$ in which each $U_i$ is 1-strongly Euclidean in $X$ and
--   $$e_{\max}=\max_i e(U_i)\ge\frac12(\log_2k)^{1/4}=\Omega\bigl(\sqrt[4]{\log k}\bigr).$$
--   Here $e(U_i)$ is the Lipschitz extension constant of $U_i$ in $X$, at least $1$ by definition.
--
--   Differences from the source:
--   - encoding: e_max = max_i e(U_i) → the published eMax (max of 1 and the extension constants of the nonempty U_i), in ℝ≥0∞; reason: e(V) ≥ 1 by definition, so the outer max with 1 changes nothing; empty members have no constant in the source
--   - encoding: ½(log₂ k)^{1/4} = Ω(⁴√log k) → ENNReal.ofReal (½ · (Real.logb 2 k)^{1/4}) ≤ eMax U; reason: the Ω form is an arithmetic restatement of the explicit bound, which is stated in full
--   - encoding: a finite metric space X = U1 ∪ … ∪ Uk → some X : Type with a MetricSpace and Finite instance and U : Fin k → Set X covering X; reason: the existential ranges over exactly the source's finite metric spaces
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 25, §6, Theorem 6.1 (proof §6.3, p. 27)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Theorem 6.1, p. 25: for every `k ≥ 2`, a finite metric space covered by `k` 1-strongly
Euclidean sets with `e_max ≥ ½ (log₂ k)^{1/4}`. -/
theorem theorem_6_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : Finite X) (U : Fin k → Set X),
      Covers U ∧ (∀ i, OneStrong (U i)) ∧
      ENNReal.ofReal ((1/2) * (Real.logb 2 k) ^ (1/4 : ℝ)) ≤ eMax U := by sorry

end BourgainUnion.Euclidean.Supplement
