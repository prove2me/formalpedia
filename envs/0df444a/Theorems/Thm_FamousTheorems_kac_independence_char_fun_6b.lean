-- Prove2me | Theorems.Thm_FamousTheorems_kac_independence_char_fun_6b
-- name    : FamousTheorems.kac_independence_char_fun_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:48.418794+00:00
-- url     : https://prove2.me/theorems/62441838-74b3-4719-8488-f8620048db2e
-- title:
--   Kac's theorem: independence via characteristic functions
-- statement:
--   **Kac's theorem: independence via characteristic functions.** Let $X_1,\dots,X_n$ be random variables on a probability space, where $X_i$ takes values in a separable real Hilbert space $E_i$. Then $X_1,\dots,X_n$ are independent if and only if, for all $t=(t_1,\dots,t_n)$,
--   $$\varphi_{(X_1,\dots,X_n)}(t)=\prod_{i=1}^n\varphi_{X_i}(t_i),$$
--   where $\varphi_Y(t)=\mathbb E\,e^{i\langle t,Y\rangle}$ is the characteristic function.
--
--   This is a convenient test for independence: the joint characteristic function factors exactly when the variables are independent. It is used to show that uncorrelated jointly Gaussian variables are independent and in Fourier-analytic proofs of limit theorems.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.iIndepFun_iff_charFun_pi`. The random vector is viewed in `WithLp 2 (∀ i, E i)`, the product with the $L^2$ inner product $\langle s,t\rangle=\sum_i\langle s_i,t_i\rangle$. `charFun μ t` is $\int e^{i\langle x,t\rangle}\,d\mu(x)$, and `P.map Y` is the law of $Y$. Each $X_i$ is assumed almost everywhere measurable.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.iIndepFun_iff_charFun_pi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem kac_independence_char_fun_6b {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype ι] [IsProbabilityMeasure P]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : ∀ i, Ω → E i} (hX : ∀ i, AEMeasurable (X i) P) :
    ProbabilityTheory.iIndepFun X P ↔
      ∀ t : WithLp 2 (∀ i, E i),
        charFun (P.map fun ω => WithLp.toLp 2 fun i => X i ω) t = ∏ i, charFun (P.map (X i)) (t.ofLp i) := by sorry

end FamousTheorems
