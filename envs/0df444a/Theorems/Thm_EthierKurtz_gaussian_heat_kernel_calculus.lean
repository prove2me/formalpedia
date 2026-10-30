-- Prove2me | Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
-- name    : EthierKurtz.gaussian_heat_kernel_calculus
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:14:29.122156+00:00
-- url     : https://prove2.me/theorems/30e19e83-ea43-4787-8e8d-11b5e806eddf
-- title:
--   Gaussian heat kernel: derivative formulas, Gaussian bounds and reflection estimates
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. Then: $g_a>0$; the derivatives of $g_a$ are $$g^{(1)}_a(z)v=-2a\,g_a(z)\langle z,v\rangle,\quad g^{(2)}_a(z)(v,w)=g_a(z)\big(4a^2\langle z,v\rangle\langle z,w\rangle-2a\langle v,w\rangle\big)$$ and the corresponding third-order formula, with $g^{(2)}_a$ smooth; $G_s=(\pi s)^{-d/2}g_{1/s}$; $w$ is three times differentiable in $x$ with the Gaussian bounds $|\partial_x^jw(t,x,y)|\le A\,t^{-j/2}G_{4t}(x-y)$ ($j\le3$); $\langle R_ex,e\rangle=-\langle x,e\rangle$, $|x-R_ey|^2=|x-y|^2+4\langle x,e\rangle\langle y,e\rangle$ and $G_s(x-R_ey)\le G_s(x-y)$ on the half-space; $G_s\le(s'/s)^{d/2}G_{s'}$ for $s\le s'$; and the ray estimate $G_\sigma(z+s(e-b))\le r_K(b)^{d/2}e^{m^2/\sigma}G_{r_K(b)\sigma}(z)e^{-s^2/(r_K(b)\sigma)}$ when $\langle z,e\rangle\ge-m$.
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1 (the fundamental solution of the heat equation and Gaussian bounds for its derivatives), ; D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (half-space model, reflection); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem gaussian_heat_kernel_calculus :
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
  let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
  let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
  let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
  let wK3 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK3 (1 / (2 * t)) (x - y));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
  let rK : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (14 + 8 * ‖b‖ ^ 2);
  let rC : (b : EuclideanSpace ℝ (Fin d)) → (m σ : ℝ) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ) => (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2));
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), 0 < ge a z) ∧
    (∀ (a : ℝ) (z v : EuclideanSpace ℝ (Fin d)), gK1 a z v = -(2 * a) * ge a z * inner ℝ z v) ∧
    (∀ (a : ℝ) (z v w : EuclideanSpace ℝ (Fin d)), gK2 a z v w = ge a z * (4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w)) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (ge a) (gK1 a z) z) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (gK1 a) (gK2 a z) z) ∧
    (∀ (a : ℝ), ContDiff ℝ ⊤ (gK2 a)) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (gK2 a) (gK3 a z) z) ∧
    (∀ (a : ℝ) (z u v w : EuclideanSpace ℝ (Fin d)), gK3 a z u v w = ge a z * (-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w + inner ℝ z v * inner ℝ u w))) ∧
    (∀ (s : ℝ) (z : EuclideanSpace ℝ (Fin d)), G s z = (π * s) ^ (-((d : ℝ) / 2)) * ge (1 / s) z) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK t x y) (wK1 t x y) x) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK1 t x y) (wK2 t x y) x) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK2 t x y) (wK3 t x y) x) ∧
    (∀ {t : ℝ} (ht : 0 < t), 0 < hN t) ∧
    (∀ {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin d)), hN t * ge (1 / (2 * t)) z = G (2 * t) z) ∧
    (0 ≤ wA) ∧
    (∀ {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), |wK t x y| ≤ wA * G (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * G (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA * t ^ (-(1 : ℝ)) * G (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA * t ^ (-(3 / 2 : ℝ)) * G (4 * t) (x - y)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), inner ℝ e e = (1 : ℝ)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x : EuclideanSpace ℝ (Fin d)), inner ℝ (Rf e x) e = -inner ℝ x e) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x y : EuclideanSpace ℝ (Fin d)), ‖x - Rf e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {x y : EuclideanSpace ℝ (Fin d)} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), G s (x - Rf e y) ≤ G s (x - y)) ∧
    (∀ {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (z : EuclideanSpace ℝ (Fin d)), G s z ≤ (s' / s) ^ ((d : ℝ) / 2) * G s' z) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)), 1 ≤ rK b) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)), 0 < rK b) ∧
    (∀ {e b z : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ), 0 ≤ rC b m σ) := by sorry

end EthierKurtz
