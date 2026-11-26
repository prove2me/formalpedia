-- Prove2me | Theorems.Thm_Arxiv2507_18491_reaction_component_unified_representation
-- name    : Arxiv2507_18491.reaction_component_unified_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:01:04.386787+00:00
-- url     : https://prove2.me/theorems/daa374dc-b9f9-48c9-8b88-a13597e2db16
-- title:
--   Eq. (3.18): unified integral representation of the reaction field components (as proved)
-- statement:
--   Let the layered medium have interfaces $d_0>\dots>d_{L-1}$, frequency $\omega>0$, and $\varepsilon_j,\mu_j>0$. Let $\ell,\ell'\le L$, and let $(\ast,\star)$ be a defined reaction field component with densities $\phi=\phi^{\ast\star}_{\ell\ell'}$ and $\psi=\psi^{\ast\star}_{\ell\ell'}$.
--
--   1. For $k_\rho>0$ and $k_x=k_\rho\cos\alpha$, $k_y=k_\rho\sin\alpha$:
--   $$J_1+\tfrac{1}{k_\rho^2}J_5=M_1+e^{2\mathrm i\alpha}M_2+e^{-2\mathrm i\alpha}M_3,\quad J_2=M_6,\quad -\tfrac{\mathrm i}{k_\rho}J_3=e^{\mathrm i\alpha}M_4+e^{-\mathrm i\alpha}M_5,$$
--   $$-\tfrac{\mathrm i}{k_\rho}J_4=e^{\mathrm i\alpha}M_4^{\rm T}+e^{-\mathrm i\alpha}M_5^{\rm T},\quad -\tfrac{1}{k_\rho^2}J_5=M_1-e^{2\mathrm i\alpha}M_2-e^{-2\mathrm i\alpha}M_3.$$
--   2. If moreover $k_{\ell'z}\neq0$, $z$ lies in layer $\ell$ and $z'$ lies in layer $\ell'$, then
--   $$\widehat{\boldsymbol G}^{\ast\star}_{\ell\ell'}=\frac{\mathrm i}{2}Z^{\ast\star}_{\ell\ell'}\Big(\sigma_1M_1+\sigma_3^{c}e^{2\mathrm i\alpha}M_2+\sigma_3^{c}e^{-2\mathrm i\alpha}M_3+\sigma_2e^{\mathrm i\alpha}M_4+\sigma_2e^{-\mathrm i\alpha}M_5+\sigma_4e^{\mathrm i\alpha}M_4^{\rm T}+\sigma_4e^{-\mathrm i\alpha}M_5^{\rm T}+\sigma_5M_6\Big).$$
--   3. Let $\boldsymbol r=(x,y,z)$ with $z$ in layer $\ell$ and $\boldsymbol r'=(x',y',z')$ with $z'$ in layer $\ell'$. Suppose the eight integrands $\mathcal E(\hat\tau(\boldsymbol r),\breve\tau(\boldsymbol r'))e^{\mathrm i\kappa\alpha}\sigma(k_\rho)$ that occur below are Lebesgue integrable on $\mathbb R^2$. Then the inverse Fourier transform $\boldsymbol G^{\ast\star}_{\ell\ell'}(\boldsymbol r,\boldsymbol r')=\frac1{4\pi^2}\iint\widehat{\boldsymbol G}^{\ast\star}_{\ell\ell'}e^{\mathrm ik_x(x-x')+\mathrm ik_y(y-y')}dk_xdk_y$ satisfies (3.18):
--   $$\boldsymbol G^{\ast\star}_{\ell\ell'}=\mathcal L_0[\sigma_1]M_1+\mathcal L_2[\sigma_3^{c}]M_2+\mathcal L_{-2}[\sigma_3^{c}]M_3+\mathcal L_1[\sigma_2]M_4+\mathcal L_{-1}[\sigma_2]M_5+\mathcal L_1[\sigma_4]M_4^{\rm T}+\mathcal L_{-1}[\sigma_4]M_5^{\rm T}+\mathcal L_0[\sigma_5]M_6,$$
--   with $\mathcal L_\kappa=\mathcal L^{\ast\star}_{\ell\ell'\kappa}$ the operator (3.19).
--
--   Here $\sigma_1,\sigma_2,\sigma_4,\sigma_5$ are the densities (3.16)-(3.17), and $\sigma_3^c$ is $\phi/k_{\ell'z}+\gamma_{\ell\ell'}k_{\ell z}\psi$ for $\uparrow\downarrow,\downarrow\uparrow$ and $\phi/k_{\ell'z}-\gamma_{\ell\ell'}k_{\ell z}\psi$ for $\uparrow\uparrow,\downarrow\downarrow$. This representation puts all the dependence on the polar angle $\alpha$ into five factors $e^{\mathrm i\kappa\alpha}$, and the paper's far-field expansions are built on it.
--
--   **Formalization Note** This is stated as proved, not as printed. Substituting the matrix identities into (3.14) gives the coefficient $\sigma_3^c$ of $M_2,M_3$. The printed (3.16) sets $\sigma^{\ast\downarrow}_{\ell\ell'3}=\phi/k_{\ell'z}+\gamma k_{\ell z}\psi$ and $\sigma^{\ast\uparrow}_{\ell\ell'3}=\phi/k_{\ell'z}-\gamma k_{\ell z}\psi$, which agrees with $\sigma_3^c$ for $\uparrow\downarrow,\uparrow\uparrow$ and has the wrong sign of the $\psi$ term for $\downarrow\uparrow,\downarrow\downarrow$. The integrals are Lebesgue integrals, and their absolute convergence is assumed. The step from $\widehat{\boldsymbol G}$ to $\mathcal E(\hat\tau,\breve\tau)$ uses the fact that $Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z')=e^{s^{\ast\star}_{\ell\ell'}(\mathrm ik_{\ell z}\hat z-\mathrm ik_{\ell'z}\breve z)}$.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c005; Section 3.1, matrices and identities after eq. (3.15), eqs. (3.16)-(3.17), the spectral display after (3.17), and eqs. (3.18)-(3.23), PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem reaction_component_unified_representation (omega : ℝ) (epsL muL : ℕ → ℝ)
    (homega : 0 < omega) (heps : ∀ j, 0 < epsL j) (hmu : ∀ j, 0 < muL j) (L : ℕ)
    (d : ℕ → ℝ) (hd : IsInterfaces L d) (l l' : ℕ) (hl : l ≤ L) (hl' : l' ≤ L) (a b : Dir)
    (hab : CompDefined L l l' a b) (phiD psiD : ℝ → ℂ) :
    (∀ krho alpha : ℝ, 0 < krho →
      J1 + ((krho : ℂ) ^ 2)⁻¹ • J5 (krho * Real.cos alpha) (krho * Real.sin alpha) =
          M1 + Complex.exp (2 * alpha * Complex.I) • M2
            + Complex.exp (-2 * alpha * Complex.I) • M3 ∧
      J2 = M6 ∧
      (-Complex.I / (krho : ℂ)) • J3 (krho * Real.cos alpha) (krho * Real.sin alpha) =
          Complex.exp (alpha * Complex.I) • M4 + Complex.exp (-alpha * Complex.I) • M5 ∧
      (-Complex.I / (krho : ℂ)) • J4 (krho * Real.cos alpha) (krho * Real.sin alpha) =
          Complex.exp (alpha * Complex.I) • M4.transpose
            + Complex.exp (-alpha * Complex.I) • M5.transpose ∧
      (-((krho : ℂ) ^ 2)⁻¹) • J5 (krho * Real.cos alpha) (krho * Real.sin alpha) =
          M1 - Complex.exp (2 * alpha * Complex.I) • M2
            - Complex.exp (-2 * alpha * Complex.I) • M3) ∧
    (∀ krho alpha z z' : ℝ, 0 < krho → vkz (waveNum omega epsL muL l') krho ≠ 0 →
      InLayer L d l z → InLayer L d l' z' →
      GhatReac (waveNum omega epsL muL) muL d l l' a b phiD psiD
          (krho * Real.cos alpha) (krho * Real.sin alpha) z z' =
        (Complex.I / 2 * Zfun (waveNum omega epsL muL) d l l' a b krho z z') •
          (sig1 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
              a b phiD psiD krho • M1
            + (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a b phiD psiD krho * Complex.exp (2 * alpha * Complex.I)) • M2
            + (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a b phiD psiD krho * Complex.exp (-2 * alpha * Complex.I)) • M3
            + (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a psiD krho * Complex.exp (alpha * Complex.I)) • M4
            + (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a psiD krho * Complex.exp (-alpha * Complex.I)) • M5
            + (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD krho
                * Complex.exp (alpha * Complex.I)) • M4.transpose
            + (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD krho
                * Complex.exp (-alpha * Complex.I)) • M5.transpose
            + sig5 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                psiD krho • M6)) ∧
    (∀ r r' : ℝ × ℝ × ℝ, InLayer L d l r.2.2 → InLayer L d l' r'.2.2 →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b 0
        (sig1 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          a b phiD psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b 2
        (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          a b phiD psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b (-2)
        (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          a b phiD psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b 1
        (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          a psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b (-1)
        (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          a psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b 1
        (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b (-1)
        (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD) r r') →
      Integrable (opLIntegrand (waveNum omega epsL muL) d l l' a b 0
        (sig5 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
          psiD) r r') →
      ∀ i j : Fin 3,
        GReac (waveNum omega epsL muL) muL d l l' a b phiD psiD r r' i j =
          opL (waveNum omega epsL muL) d l l' a b 0
              (sig1 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a b phiD psiD) r r' * M1 i j
            + opL (waveNum omega epsL muL) d l l' a b 2
              (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a b phiD psiD) r r' * M2 i j
            + opL (waveNum omega epsL muL) d l l' a b (-2)
              (sig3c (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a b phiD psiD) r r' * M3 i j
            + opL (waveNum omega epsL muL) d l l' a b 1
              (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a psiD) r r' * M4 i j
            + opL (waveNum omega epsL muL) d l l' a b (-1)
              (sig2 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                a psiD) r r' * M5 i j
            + opL (waveNum omega epsL muL) d l l' a b 1
              (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD) r r' * M4.transpose i j
            + opL (waveNum omega epsL muL) d l l' a b (-1)
              (sig4 (waveNum omega epsL muL l) (muL l) (muL l') b psiD) r r' * M5.transpose i j
            + opL (waveNum omega epsL muL) d l l' a b 0
              (sig5 (waveNum omega epsL muL l) (waveNum omega epsL muL l') (muL l) (muL l')
                psiD) r r' * M6 i j) := by sorry

end Arxiv2507_18491
