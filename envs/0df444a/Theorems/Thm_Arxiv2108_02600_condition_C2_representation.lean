-- Prove2me | Theorems.Thm_Arxiv2108_02600_condition_C2_representation
-- name    : Arxiv2108_02600.condition_C2_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:05:00.832111+00:00
-- url     : https://prove2.me/theorems/2a5b9813-fdf8-491c-8cce-fdc5d63333fd
-- title:
--   Proof of Theorem 4.1, eqs. (4.3)–(4.9): condition C2 for $C^*$ (as proved)
-- statement:
--   Let $\operatorname{Re}\eta>0$, $h<c$, $M>0$, $n\ge1$ and $f\in B^{(n)}_{c,M}$. Use the notation $\rho_m(\kappa,s,t)=H^{(1)}_m(\kappa r)-\frac{2i}\pi J_m(\kappa r)\ln|s-t|$, $\gamma_1,\gamma_2,\gamma_3,\xi,\zeta_{jk},\sigma_{jk}$ of the proof of Theorem 4.1, $\phi(0)=0$, $\phi(p)=\sum_{m=1}^p\frac1m$, and
--
--   $$L(\kappa)=1+\frac{2i}{\pi}C_E+\frac{2i}{\pi}\ln\frac{\kappa r}{2|s-t|}.$$
--
--   For $s\ne t$ and $j,k=1,2$:
--
--   1. (4.3) $C^*_{jk}=-i\eta\big\{[\frac{i}{2\mu}\rho_0(\kappa_s)-\frac{i}{2\omega^2}\gamma_1]\delta_{jk}+\frac{i}{2\omega^2}\gamma_2\zeta_{jk}\big\}\sqrt{1+f'(t)^2}+(\mu+\tilde\mu)\big\{[-\frac{i}{2\mu}\kappa_sr\rho_1(\kappa_s)+\frac{i}{2\omega^2}\gamma_2]\delta_{jk}-\frac{i}{2\omega^2}\gamma_3\zeta_{jk}\big\}\xi+\sigma_{jk}-A^{(3)}_{jk}$.
--   2. (4.4) For every $\kappa>0$, $\rho_0(\kappa)=L(\kappa)J_0(\kappa r)-\frac{2i}\pi\sum_{p\ge0}\frac{(-1)^p}{(p!)^2}(\frac{\kappa r}2)^{2p}\phi(p)$.
--   3. (4.5) $\kappa_sr\rho_1(\kappa_s)=L(\kappa_s)\kappa_srJ_1(\kappa_sr)-\frac{2i}\pi-\frac{2i}\pi\sum_{p\ge0}\frac{(-1)^p}{p!(p+1)!}(\frac{\kappa_sr}2)^{2+2p}(\phi(p+1)+\phi(p))$.
--   4. (4.6) $\gamma_1=\kappa_sL(\kappa_s)\frac{J_1(\kappa_sr)}r-\kappa_pL(\kappa_p)\frac{J_1(\kappa_pr)}r-\frac{i}{2\pi}\sum_{p\ge0}\frac{(-1)^p}{p!(p+1)!}(\frac r2)^{2p}(\kappa_s^{2+2p}-\kappa_p^{2+2p})(\phi(p)+\phi(p+1))$.
--   5. (4.7) $\gamma_2=\kappa_s^2L(\kappa_s)J_2(\kappa_sr)-\kappa_p^2L(\kappa_p)J_2(\kappa_pr)-\frac i\pi(\kappa_s^2-\kappa_p^2)-\frac i\pi\sum_{p\ge0}\frac{(-1)^p}{p!(p+2)!}(\frac r2)^{2+2p}(\kappa_s^{4+2p}-\kappa_p^{4+2p})(\phi(p)+\phi(p+2))$.
--   6. (4.8) $\gamma_3=\kappa_s^3rL(\kappa_s)J_3(\kappa_sr)-\kappa_p^3rL(\kappa_p)J_3(\kappa_pr)-\frac{2i}\pi(\kappa_s^2-\kappa_p^2)-\frac{ir^2}{4\pi}(\kappa_s^4-\kappa_p^4)-\frac{ir}\pi\sum_{p\ge0}\frac{(-1)^p}{p!(p+3)!}(\frac r2)^{3+2p}(\kappa_s^{6+2p}-\kappa_p^{6+2p})(\phi(p)+\phi(p+3))$.
--   7. (4.9) $\sigma_{jk}$ equals the right side of (4.9), with $-\frac{ir}{4\pi}(\kappa_s^4-\kappa_p^4)$ in its last brace.
--   8. Regularity. The following extend from $\{s\ne t\}$ to functions in $BC^n(\mathbb R^2)$: $r/|s-t|$, $\zeta_{jk}$, $\xi$, $\rho_0(\kappa)$ for every $\kappa>0$, $\gamma_1$, $\gamma_2$, $\sigma_{jk}$, $C^*_{jk}$, $B^{(1)}_{jk}$ and $B^{(2)}_{jk}$. Also $\sqrt{1+f'^2}\in BC^n(\mathbb R)$. The functions $\kappa_sr\rho_1(\kappa_s)$ and $\gamma_3$ extend to $C^n$ functions on $\mathbb R^2$ whose derivatives of order $\le n$ are bounded on the strip $|s-t|\le\pi$.
--
--   Together these give conditions C1 and C2 of the proof of Theorem 4.1.
--
--   **Formalization Note** This is the version the proof establishes. Three changes from the printed text: (a) in (4.8) the term is $-\frac{ir^2}{4\pi}(\kappa_s^4-\kappa_p^4)$, where the paper prints $-\frac{ir}{4\pi}(\kappa_s^4-\kappa_p^4)$; (b) in the last brace of (4.9) it is $-\frac{ir}{4\pi}(\kappa_s^4-\kappa_p^4)$, where the paper prints $-\frac{i}{4\pi}(\kappa_s^4-\kappa_p^4)$; the printed forms fail numerically, and the forms here follow from the series that the paper cites; (c) the paper puts $\kappa_sr\rho_1(\kappa_s)$ and $\gamma_3$ in $BC^n(\mathbb R^2)$, but they grow like $\sqrt r\ln r$ as $|s-t|\to\infty$. Their bounds are therefore stated on $|s-t|\le\pi$, the region where condition C2 is used.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c011; Section 4, proof of Theorem 4.1, notation before (4.3), eqs. (4.3)-(4.9) and the regularity statements after (4.9), PDF pp. 14-16

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem condition_C2_representation (P : Lame) (η : ℂ) (hη : 0 < η.re) (h c M : ℝ) (hhc : h < c)
    (hM : 0 < M) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) (hf : InB n c M f) :
    let I := Complex.I
    let pi : ℂ := (Real.pi : ℂ)
    let ks : ℂ := (P.ks : ℂ)
    let kp : ℂ := (P.kp : ℂ)
    let mu : ℂ := (P.mu : ℂ)
    let om2 : ℂ := (P.omega : ℂ) ^ 2
    let R : ℝ → ℝ → ℂ := fun s t => (rdist f s t : ℂ)
    let J : ℕ → ℝ → ℝ → ℝ → ℂ := fun m κ s t => (besselJ m (κ * rdist f s t) : ℂ)
    let L : ℝ → ℝ → ℝ → ℂ := fun κ s t =>
      1 + 2 * I / pi * (Real.eulerMascheroniConstant : ℂ) +
        2 * I / pi * (Real.log (κ * rdist f s t / (2 * |s - t|)) : ℂ)
    let ph : ℕ → ℂ := fun p => (phiH p : ℂ)
    let fac : ℕ → ℂ := fun p => (p.factorial : ℂ)
    let dl : Fin 2 → Fin 2 → ℂ := fun j k => if j = k then 1 else 0
    let ExtBC : (ℝ → ℝ → ℂ) → Prop := fun F =>
      ∃ G : ℝ × ℝ → ℂ, IsBCn n G ∧ ∀ s t : ℝ, s ≠ t → G (s, t) = F s t
    let ExtBCstrip : (ℝ → ℝ → ℂ) → Prop := fun F =>
      ∃ G : ℝ × ℝ → ℂ, ContDiff ℝ n G ∧ (∀ s t : ℝ, s ≠ t → G (s, t) = F s t) ∧
        ∀ m ≤ n, ∃ K : ℝ, ∀ s t : ℝ, |s - t| ≤ Real.pi → ‖iteratedFDeriv ℝ m G (s, t)‖ ≤ K
    -- (4.3)
    (∀ s t : ℝ, s ≠ t → ∀ j k : Fin 2,
      kerCstar P η h f s t j k =
        -(I * η) * ((dl j k * (I / (2 * mu) * rhoN f 0 P.ks s t - I / (2 * om2) * gam1 P f s t) +
            I / (2 * om2) * gam2 P f s t * (zetaF f s t j k : ℂ)) * (jac f t : ℂ))
        + ((P.mu + P.muT : ℝ) : ℂ) *
            ((dl j k * (-(I / (2 * mu)) * ks * R s t * rhoN f 1 P.ks s t + I / (2 * om2) * gam2 P f s t) -
              I / (2 * om2) * gam3 P f s t * (zetaF f s t j k : ℂ)) * (xiF f s t : ℂ))
        + sigmaF P f s t j k - kerA3 P η h f s t j k) ∧
    -- (4.4)
    (∀ κ : ℝ, 0 < κ → ∀ s t : ℝ, s ≠ t →
      rhoN f 0 κ s t = L κ s t * J 0 κ s t -
        2 * I / pi * ∑' p : ℕ, (-1 : ℂ) ^ p / fac p ^ 2 * ((κ : ℂ) * R s t / 2) ^ (2 * p) * ph p) ∧
    -- (4.5)
    (∀ s t : ℝ, s ≠ t →
      ks * R s t * rhoN f 1 P.ks s t = L P.ks s t * ks * R s t * J 1 P.ks s t - 2 * I / pi -
        2 * I / pi * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 1)) * (ks * R s t / 2) ^ (2 + 2 * p) *
          (ph (p + 1) + ph p)) ∧
    -- (4.6)
    (∀ s t : ℝ, s ≠ t →
      gam1 P f s t = ks * L P.ks s t * J 1 P.ks s t / R s t - kp * L P.kp s t * J 1 P.kp s t / R s t -
        I / (2 * pi) * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 1)) * (R s t / 2) ^ (2 * p) *
          (ks ^ (2 + 2 * p) - kp ^ (2 + 2 * p)) * (ph p + ph (p + 1))) ∧
    -- (4.7)
    (∀ s t : ℝ, s ≠ t →
      gam2 P f s t = ks ^ 2 * L P.ks s t * J 2 P.ks s t - kp ^ 2 * L P.kp s t * J 2 P.kp s t -
        I / pi * (ks ^ 2 - kp ^ 2) -
        I / pi * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 2)) * (R s t / 2) ^ (2 + 2 * p) *
          (ks ^ (4 + 2 * p) - kp ^ (4 + 2 * p)) * (ph p + ph (p + 2))) ∧
    -- (4.8), with the term `-(i r²/(4π))(κ_s⁴ - κ_p⁴)` that the series gives
    (∀ s t : ℝ, s ≠ t →
      gam3 P f s t = ks ^ 3 * R s t * L P.ks s t * J 3 P.ks s t -
        kp ^ 3 * R s t * L P.kp s t * J 3 P.kp s t - 2 * I / pi * (ks ^ 2 - kp ^ 2) -
        I * R s t ^ 2 / (4 * pi) * (ks ^ 4 - kp ^ 4) -
        I * R s t / pi * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 3)) * (R s t / 2) ^ (3 + 2 * p) *
          (ks ^ (6 + 2 * p) - kp ^ (6 + 2 * p)) * (ph p + ph (p + 3))) ∧
    -- (4.9), with the term `-(i r/(4π))(κ_s⁴ - κ_p⁴)` in the last brace that the series gives
    (∀ s t : ℝ, s ≠ t → ∀ j k : Fin 2,
      let d := dvec f s t
      sigmaF P f s t j k =
        1 / pi * (((P.lam + P.mu) / (P.lam + 3 * P.mu) : ℝ) : ℂ) * (xiF f s t : ℂ) * dl j k
        + I / (2 * mu) *
            (((P.lamT * (d j * lvec f t k) -
              P.muT * (((f s - f t) * (if j = 0 then 1 else 0) - (s - t) * (if j = 1 then 1 else 0)) *
                lperp f t k)) : ℝ) : ℂ) *
            (ks * L P.ks s t * J 1 P.ks s t / R s t -
              I * ks ^ 2 / (2 * pi) * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 1)) *
                (ks * R s t / 2) ^ (2 * p) * (ph p + ph (p + 1)))
        - I / (2 * om2) *
            ((((P.mu + P.muT) * (d j * lvec f t k + d k * lvec f t j) + 4 * P.lamT * (d j * lvec f t k)) :
              ℝ) : ℂ) *
            (ks ^ 2 * L P.ks s t * J 2 P.ks s t / R s t ^ 2 - kp ^ 2 * L P.kp s t * J 2 P.kp s t / R s t ^ 2 -
              I / (4 * pi) * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 2)) * (R s t / 2) ^ (2 * p) *
                (ks ^ (4 + 2 * p) - kp ^ (4 + 2 * p)) * (ph p + ph (p + 2)))
        + I * (P.lamT : ℂ) / (2 * om2) * ((d j * lvec f t k : ℝ) : ℂ) / R s t *
            (ks ^ 3 * L P.ks s t * J 3 P.ks s t - kp ^ 3 * L P.kp s t * J 3 P.kp s t -
              I * R s t / (4 * pi) * (ks ^ 4 - kp ^ 4) -
              I / pi * ∑' p : ℕ, (-1 : ℂ) ^ p / (fac p * fac (p + 3)) * (R s t / 2) ^ (3 + 2 * p) *
                (ks ^ (6 + 2 * p) - kp ^ (6 + 2 * p)) * (ph p + ph (p + 3)))) ∧
    -- regularity: the auxiliary functions and C*, B^(1), B^(2) extend to the diagonal as BC^n
    -- functions; γ₃ and κ_s r ρ₁ have bounded derivatives on the strip |s - t| ≤ π
    ExtBC (fun s t => ((rdist f s t / |s - t| : ℝ) : ℂ)) ∧ IsBCn n (jac f) ∧
    (∀ j k : Fin 2, ExtBC (fun s t => (zetaF f s t j k : ℂ))) ∧ ExtBC (fun s t => (xiF f s t : ℂ)) ∧
    (∀ κ : ℝ, 0 < κ → ExtBC (rhoN f 0 κ)) ∧
    ExtBCstrip (fun s t => ks * R s t * rhoN f 1 P.ks s t) ∧
    ExtBC (gam1 P f) ∧ ExtBC (gam2 P f) ∧ ExtBCstrip (gam3 P f) ∧
    (∀ j k : Fin 2, ExtBC (fun s t => sigmaF P f s t j k)) ∧
    (∀ j k : Fin 2, ExtBC (fun s t => kerCstar P η h f s t j k)) ∧
    (∀ j k : Fin 2, ExtBC (fun s t => kerB1 P f s t j k)) ∧
    (∀ j k : Fin 2, ExtBC (fun s t => kerB2 P f s t j k)) := by sorry

end Arxiv2108_02600
