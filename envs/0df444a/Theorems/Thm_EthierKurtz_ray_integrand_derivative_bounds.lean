-- Prove2me | Theorems.Thm_EthierKurtz_ray_integrand_derivative_bounds
-- name    : EthierKurtz.ray_integrand_derivative_bounds
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:03:47.868415+00:00
-- url     : https://prove2.me/theorems/1dd29b5a-7b09-4d8a-bda1-bec2e8aeac12
-- title:
--   Derivatives of the oblique ray integrand and their Gaussian bounds
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. For $|e|=1$, $\langle b,e\rangle=0$, let $P_j(b,t,w)$ be the $j$-th $w$-derivative of the directional derivative $P_0(b,t,w)=h_N(t)\,\partial_b g_{1/(2t)}(w)$ of the heat kernel, and the ray kernels $$r_j(t,x,y)=\int_0^\infty P_j\big(b,t,\,x-R_ey+s(e-b)\big)\,ds ,\qquad H_e=\{y:\langle y,e\rangle\ge0\}.$$ Then $P_0,P_1,P_2$ are differentiable in $w$ with derivatives $P_1,P_2,P_3$ and $$\|P_j(b,t,w)\|\le 2A|b|\,t^{-(j+1)/2}G_{4t}(w)\qquad(j\le3,\ t>0).$$
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1 (derivatives of the fundamental solution); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (oblique derivative problem, half-space model); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem ray_integrand_derivative_bounds :
    ∀ (d : ℕ),
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      let G : (s : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s));
      let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
      let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
      let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
      let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
      let gK3 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK2 a) z);
      let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
      let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
      let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
      let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
      let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
      let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
      let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
      let rP1 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb2 b (gK2 (1 / (2 * t)) w));
      let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
      let rP3 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • (eb3 b).comp (gK4 (1 / (2 * t)) w));
        (∀ (b : EuclideanSpace ℝ (Fin d)) (M : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), eb1 b M = M b) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP0 b t) (rP1 b t w) w) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP1 b t) (rP2 b t w) w) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP2 b t) (rP3 b t w) w) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ (Fin d)), |rP0 b t w| ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * G (4 * t) w ∧ ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 : ℝ)) * G (4 * t) w ∧ ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(3 / 2 : ℝ)) * G (4 * t) w ∧ ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(2 : ℝ)) * G (4 * t) w) := by sorry

end EthierKurtz
