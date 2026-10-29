-- Prove2me | Theorems.Thm_EthierKurtz_heat_extension_holder_estimates
-- name    : EthierKurtz.heat_extension_holder_estimates
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:23:24.962585+00:00
-- url     : https://prove2.me/theorems/f5821902-cab6-4e4d-b775-0aaeed32bed8
-- title:
--   Hölder estimates for the heat extension
-- statement:
--   Let $d\ge0$, $G_s(z)=(\pi s)^{-d/2}e^{-|z|^2/s}$ ($s>0$), $g_a(z)=e^{-a|z|^2}$ with its first, second and third Fréchet derivatives $g^{(1)}_a,g^{(2)}_a,g^{(3)}_a$, $h_N(t)=(2\pi t)^{-d/2}$, the heat kernel $w(t,x,y)=G_{2t}(x-y)$ with its $x$-derivatives $w_1,w_2,w_3$, the constant $A=51\cdot2^{d/2}$, the reflection $R_ex=x-2\langle x,e\rangle e$ and the ray constants $r_K(b)=14+8|b|^2$, $r_C(b,m,\sigma)=r_K(b)^{d/2}e^{m^2/\sigma}\sqrt{\pi r_K(b)\sigma}/2$. For $|e|=1$, $0<\mu\le1$ and $h$ bounded and $\mu$-Hölder (constant $H$), let $F(y)=h_{\langle y,e\rangle^2}(y)$ (heat smoothing at time $\langle y,e\rangle^2$, $F=h$ on the hyperplane) and $T(x)=\langle x,e\rangle\,Dh_{\langle x,e\rangle^2}(x)$. Then $$|F(x)-F(x')|\le c_H(\mu)H|x-x'|^\mu,\qquad\|T(x)-T(x')\|\le c_T(\mu)H|x-x'|^\mu,$$ and $\|D^2h_{a}(y)\|\le A\,a^{(\mu-2)/2}H$.
--
--   **Formalization Note**: all objects are introduced by `let` in the statement; the statement is the conjunction of the listed facts, each in the exact form used later in the proof.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Lemma 6.38 and Section 4.3 (Hölder estimates); A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem heat_extension_holder_estimates :
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
      let lap2L : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := (∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))));
      let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
      let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
      let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
      let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
      let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
      let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
      let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
      let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
      let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
      let Wb : (h : EuclideanSpace ℝ (Fin d) → ℝ) → (s : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (h : EuclideanSpace ℝ (Fin d) → ℝ) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (if 0 < s then kw0 univ (wK) h s x else h x);
      let FE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => (Wb ψ (inner ℝ y e ^ 2) y);
      let cTm : (μ : ℝ) → ℝ := fun (μ : ℝ) => ((d / μ + 1) * wA * gm * 4 ^ (μ / 2));
      let cH : (μ : ℝ) → ℝ := fun (μ : ℝ) => ((2 + 2 ^ μ) * wA * gm * 4 ^ (μ / 2) + 1 + cTm μ);
      let KH1 : (μ Hh : ℝ) → ℝ := fun (μ Hh : ℝ) => (wA * gm * 4 ^ (μ / 2) * Hh);
      let TK : (e : EuclideanSpace ℝ (Fin d)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (inner ℝ x e • kw1 univ wK1 h (inner ℝ x e ^ 2) x);
      let cTK : (μ : ℝ) → ℝ := fun (μ : ℝ) => (5 * wA * gm * 4 ^ (μ / 2) + 32 * ‖lap2L‖ * wA * gm * 4 ^ μ);
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x x' : EuclideanSpace ℝ (Fin d)), |FE e h x - FE e h x'| ≤ cH μ * Hh * ‖x - x'‖ ^ μ) ∧
        (∀ {μ Hh : ℝ} (hH : 0 ≤ Hh), 0 ≤ KH1 μ Hh) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : ℝ} (ha : 0 < a) (y : EuclideanSpace ℝ (Fin d)), ‖kw2 univ wK2 h (a ^ 2) y‖ ≤ KH1 μ Hh * a ^ (μ - 2)) ∧
        (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x x' : EuclideanSpace ℝ (Fin d)), ‖TK e h x - TK e h x'‖ ≤ cTK μ * Hh * ‖x - x'‖ ^ μ) := by sorry

end EthierKurtz
