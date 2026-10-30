-- Prove2me | Theorems.Thm_EthierKurtz_heat_extension_c1mu_properties
-- name    : EthierKurtz.heat_extension_c1mu_properties
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:19:28.022473+00:00
-- url     : https://prove2.me/theorems/cd05efef-8f90-407e-82e6-194df06fc096
-- title:
--   Heat extension of a $C^{1,\mu}$ function from a hyperplane
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. For $|e|=1$ let $P_e=I-e\otimes e$, and for $\psi\in C^{1,\mu}$ (bounds $M_0,M_1$, Hölder constant $H$ of $D\psi$) define the extension $$E\psi(x)=\int_0^{\langle x,e\rangle}\psi_{\tau^2}(P_ex+\tau e)\,d\tau ,$$ ($\psi_s$ the heat smoothing). Then $\psi$ is continuous, $D_v\psi$ is $\mu$-Hölder, $E\psi=0$ on the hyperplane $\langle x,e\rangle=0$ with $DE\psi=\psi\,e^\top$ there, $E\psi$ is strictly differentiable everywhere, $DE\psi$ is continuous and differentiable where $\langle x,e\rangle>0$ ($0<\mu\le1$), with the second-derivative bounds of the statement.
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Lemma 6.37-6.38 (extension of $C^{k,\mu}$ functions) and Section 6.7; A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem heat_extension_c1mu_properties :
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
      let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
      let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
      let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
      let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
      let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
      let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
      let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
      let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
      let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
      let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
      let C1H : (μ M0 M1 H : ℝ) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → Prop := fun (μ M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) => ((∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧ (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H);
      let Wb : (h : EuclideanSpace ℝ (Fin d) → ℝ) → (s : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (h : EuclideanSpace ℝ (Fin d) → ℝ) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (if 0 < s then kw0 univ (wK) h s x else h x);
      let FE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => (Wb ψ (inner ℝ y e ^ 2) y);
      let DFE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => ((inner ℝ y e * lap2 (kw2 univ wK2 ψ (inner ℝ y e ^ 2) y)) • innerSL ℝ e + kw1 univ wK1 ψ (inner ℝ y e ^ 2) y);
      let PeL : (e : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := fun (e : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - (innerSL ℝ e).smulRight e);
      let QE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, FE e ψ (PeL e p + τ • e));
      let EXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (QE e ψ x (inner ℝ x e));
      let DQE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e));
      let DQI : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (τ : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (τ : ℝ) => ((kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e));
      let DEXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (DQE e ψ x (inner ℝ x e) + FE e ψ x • innerSL ℝ e);
      let KB : (μ H : ℝ) → ℝ := fun (μ H : ℝ) => (wA * H * gm * 4 ^ (μ / 2));
      let D2QI : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (τ : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (τ : ℝ) => (((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip (PeL e)).comp ((kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)));
      let D2QE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, D2QI e ψ p τ);
      let D2EXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (D2QE e ψ x (inner ℝ x e) + (innerSL ℝ e).smulRight (DQI e ψ x (inner ℝ x e)) + (DFE e ψ x).smulRight (innerSL ℝ e));
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1), Continuous ψ) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (v : EuclideanSpace ℝ (Fin d)), HolderOnS univ μ (M1 * ‖v‖) (H * ‖v‖) (fun y => ψ1 y v)) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (v : EuclideanSpace ℝ (Fin d)), AEStronglyMeasurable (fun y => ψ1 y v) (volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d))))) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin d)), lap2 (kw2 univ wK2 ψ s y) = ∑ i : Fin d, kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) s y (EuclideanSpace.single i 1)) ∧
        (∀ (e x : EuclideanSpace ℝ (Fin d)), PeL e x + inner ℝ x e • e = x) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x₀ : EuclideanSpace ℝ (Fin d)), HasStrictFDerivAt (EXT e ψ) (DEXT e ψ x₀) x₀) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), Continuous (DEXT e ψ)) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {e x : EuclideanSpace ℝ (Fin d)} (hx : inner ℝ x e = 0), EXT e ψ x = 0) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {e x : EuclideanSpace ℝ (Fin d)} (hx : inner ℝ x e = 0), DEXT e ψ x = ψ x • innerSL ℝ e) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1), 0 ≤ KB μ H) ∧
        (∀ (e : EuclideanSpace ℝ (Fin d)), ‖(ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip (PeL e)‖ ≤ ‖PeL e‖) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : EuclideanSpace ℝ (Fin d)} {τ : ℝ} (hτ : 0 < τ) (p : EuclideanSpace ℝ (Fin d)), ‖D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 * KB μ H * τ ^ (μ - 1)) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e p : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 ≤ c), IntervalIntegrable (fun τ => D2QI e ψ p τ) volume 0 c) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : 0 < inner ℝ x₀ e), HasFDerivAt (DEXT e ψ) (D2EXT e ψ x₀) x₀) := by sorry

end EthierKurtz
