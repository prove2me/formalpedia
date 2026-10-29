-- Prove2me | Theorems.Thm_EthierKurtz_heat_kernel_smoothing_estimates
-- name    : EthierKurtz.heat_kernel_smoothing_estimates
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:27:12.875973+00:00
-- url     : https://prove2.me/theorems/66bef1a8-80bd-44f1-8088-5d2685fb6ef8
-- title:
--   Heat-kernel smoothing: derivative, Hölder and time-difference estimates
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. For bounded measurable $\psi$ on $\mathbb{R}^d$ let $k_j(t,x)=\int\psi(y)\,\partial_x^jw(t,x,y)\,dy$ (the heat smoothing $\psi_t=\psi*G_{2t}$ and its derivatives). Then derivatives commute with smoothing ($k_1(t,x)v=\int\partial_v\psi(y)w(t,x,y)dy$ for $C^1$ bounded $\psi$, and similarly for $k_2,k_3$), and for $\mu$-Hölder $\psi$ the estimates $$|\psi_t-\psi|\le At^{\mu/2}H,\quad\|D^j\psi_t\|\le At^{(\mu-j)/2}H,\quad \partial_t\psi_t=\tfrac12\Delta\psi_t$$ and the time-difference and Lipschitz bounds of the statement hold.
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1; D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 and Lemma 6.38 (extension by smoothing); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem heat_kernel_smoothing_estimates :
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
      let gm : ℝ := (1 + 2 * 2 ^ ((d : ℝ) / 2));
      let HolderOnS : {d : ℕ} → (S : Set (EuclideanSpace ℝ (Fin d))) → (μ M0 Hh : ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → Prop := fun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (μ M0 Hh : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) => (0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ);
      let kw0 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K t x y);
      let kw1 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K1 t x y);
      let kw2 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K2 t x y);
      let kw3 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K3 t x y);
      let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
      let lap2L : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := (∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))));
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
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x v : EuclideanSpace ℝ (Fin d)), kw1 univ wK1 ψ t x v = kw0 univ (wK) (fun y => ψ1 y v) t x) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x u v : EuclideanSpace ℝ (Fin d)), kw2 univ wK2 ψ t x u v = kw1 univ wK1 (fun y => ψ1 y v) t x u) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x w u v : EuclideanSpace ℝ (Fin d)), kw3 univ wK3 ψ t x w u v = kw2 univ wK2 (fun y => ψ1 y v) t x w u) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), HasDerivAt (fun t => kw0 univ (wK) h t x) ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 h t x)) t) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw0 univ (wK) h t) (kw1 univ wK1 h t x) x) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw1 univ wK1 h t) (kw2 univ wK2 h t x) x) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw2 univ wK2 h t) (kw3 univ wK3 h t x) x) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), |kw0 univ (wK) h t x| ≤ wA * M0) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), |kw0 univ (wK) h t x - h x| ≤ wA * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), kw0 univ (wK) h s' x - kw0 univ (wK) h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 univ wK2 h σ x)) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * M0) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h s' x - kw1 univ wK1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L‖ * (wA * s ^ (-(3 / 2 : ℝ)) * Hh * (gm * (4 * s') ^ (μ / 2)))) * (s' - s)) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw2 univ wK2 h t x‖ ≤ wA * t ^ (-(1 : ℝ)) * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x x' : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))) (hx' : x' ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x - kw1 univ wK1 h t x'‖ ≤ wA * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖) := by sorry

end EthierKurtz
