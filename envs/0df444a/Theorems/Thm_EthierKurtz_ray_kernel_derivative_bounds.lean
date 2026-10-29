-- Prove2me | Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
-- name    : EthierKurtz.ray_kernel_derivative_bounds
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:07:34.576776+00:00
-- url     : https://prove2.me/theorems/a063430d-6736-4cbf-a753-ef3f917ddda5
-- title:
--   Ray kernels: differentiation under the integral and Gaussian bounds
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. For $|e|=1$, $\langle b,e\rangle=0$, let $P_j(b,t,w)$ be the $j$-th $w$-derivative of the directional derivative $P_0(b,t,w)=h_N(t)\,\partial_b g_{1/(2t)}(w)$ of the heat kernel, and the ray kernels $$r_j(t,x,y)=\int_0^\infty P_j\big(b,t,\,x-R_ey+s(e-b)\big)\,ds ,\qquad H_e=\{y:\langle y,e\rangle\ge0\}.$$ Then the $P_j$ are continuous, $r_0,r_1,r_2$ are differentiable in $x$ with derivatives $r_1,r_2,r_3$ (differentiation under the ray integral), and for $x,y\in H_e$ $$\|r_j(t,x,y)\|\le r_A(b)\,t^{-j/2}G_{4r_K(b)t}(x-y)\qquad(j\le3),$$ with $r_A(b)=2A|b|\,r_K(b)^{d/2}\sqrt{4\pi r_K(b)}/2$; a version with $\langle x-R_ey,e\rangle\ge-m$ and the constant $r_C$ also holds.
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1 (potentials and differentiation under the integral); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (oblique derivative problem, half-space model); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem ray_kernel_derivative_bounds :
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
      let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
      let rK : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (14 + 8 * ‖b‖ ^ 2);
      let rC : (b : EuclideanSpace ℝ (Fin d)) → (m σ : ℝ) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ) => (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2));
      let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
      let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
      let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
      let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
      let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
      let rP1 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb2 b (gK2 (1 / (2 * t)) w));
      let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
      let rP3 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • (eb3 b).comp (gK4 (1 / (2 * t)) w));
      let rk0 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b)));
      let rk1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP1 b t (x - Rf e y + s • (e - b)));
      let rk2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b)));
      let rk3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP3 b t (x - Rf e y + s • (e - b)));
      let rB : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (rK b ^ ((d : ℝ) / 2) * (√(π * (rK b * 4)) / 2));
      let rA : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (‖b‖ * (2 * wA) * rB b);
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP2 b t)) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP1 b t)) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP0 b t)) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ (Fin d)), ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * G (4 * t) w) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (p : ℝ), 0 ≤ ‖b‖ * (2 * wA) * t ^ p) ∧
        (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk0 e b t x y) (rk1 e b t x y) x) ∧
        (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk1 e b t x y) (rk2 e b t x y) x) ∧
        (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk2 e b t x y) (rk3 e b t x y) x) ∧
        (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t m : ℝ} (ht : 0 < t) (hm : 0 ≤ m) {x y : EuclideanSpace ℝ (Fin d)} (hxy : -m ≤ inner ℝ (x - Rf e y) e), |rk0 e b t x y| ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk1 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk2 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(3 / 2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk3 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y)) ∧
        (∀ (b : EuclideanSpace ℝ (Fin d)), 0 ≤ rA b) ∧
        (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) {x y : EuclideanSpace ℝ (Fin d)} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), |rk0 e b t x y| ≤ rA b * G (rK b * (4 * t)) (x - y) ∧ ‖rk1 e b t x y‖ ≤ rA b * t ^ (-(1 / 2 : ℝ)) * G (rK b * (4 * t)) (x - y) ∧ ‖rk2 e b t x y‖ ≤ rA b * t ^ (-(1 : ℝ)) * G (rK b * (4 * t)) (x - y) ∧ ‖rk3 e b t x y‖ ≤ rA b * t ^ (-(3 / 2 : ℝ)) * G (rK b * (4 * t)) (x - y)) := by sorry

end EthierKurtz
