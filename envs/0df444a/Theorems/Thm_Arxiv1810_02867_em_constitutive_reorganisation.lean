-- Prove2me | Theorems.Thm_Arxiv1810_02867_em_constitutive_reorganisation
-- name    : Arxiv1810_02867.em_constitutive_reorganisation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:15:45.978921+00:00
-- url     : https://prove2.me/theorems/f267f074-4ee7-5d9e-86cc-98615c5d8518
-- title:
--   Eqs. (A7)-(A16): reorganised electromagnetic constitutive relations
-- statement:
--   Let $\varepsilon_{ij},\eta_{ij},\theta_{kl},\nu_{kl},\mu_{jk}$ be real, time-independent parameters on $\mathbb R^3$. Assume $\mu_{jk}\nu_{kl}=\delta_{jl}$ (A5) and the symmetry relations (A6)
--   $$\varepsilon_{ij}=\varepsilon_{ji},\quad\nu_{kl}=\nu_{lk},\quad\mu_{jk}=\mu_{kj},\quad\eta_{ij}=-\theta_{ji}.$$
--   Let the fields $E,H,D,B$ and sources $J^{\rm e},J^{\rm m}$ satisfy the Maxwell equations (A1)-(A2) and the constitutive relations (A3)-(A4), with $E$ and $H$ differentiable in time. Then:
--
--   1. $B_j=\zeta_{jl}E_l+\mu_{jk}H_k$ and $D_i=\varepsilon^o_{il}E_l+\xi_{ik}H_k$ (A10), (A9), where $\varepsilon^o_{il}=\varepsilon_{il}-\eta_{ij}\mu_{jk}\theta_{kl}$, $\xi_{ik}=\eta_{ij}\mu_{jk}$ and $\zeta_{jl}=-\mu_{jk}\theta_{kl}$;
--   2. $\varepsilon^o_{il}=\varepsilon^o_{li}$ and $\xi_{lj}=\zeta_{jl}$ (A14);
--   3. the fields satisfy (A15)-(A16):
--   $$\varepsilon^o_{il}\partial_tE_l+\xi_{ik}\partial_tH_k-\epsilon_{ijk}\partial_jH_k=-J^{\rm e}_i,\qquad \xi_{lj}\partial_tE_l+\mu_{jk}\partial_tH_k+\epsilon_{jkl}\partial_kE_l=-J^{\rm m}_j.$$
--
--   These are the electromagnetic first-order equations that the TE and TM systems are drawn from.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c022; Appendix A.1, eqs. (A1)-(A16), PDF pp. 21-22

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem em_constitutive_reorganisation (eps eta theta nu mu : Space → Fin 3 → Fin 3 → ℝ)
    (E H D B Je Jm : Space → ℝ → Fin 3 → ℝ)
    (hmunu : ∀ x j l, ∑ k, mu x j k * nu x k l = kd j l)
    (heps : ∀ x i j, eps x i j = eps x j i) (hnu : ∀ x k l, nu x k l = nu x l k)
    (hmu : ∀ x j k, mu x j k = mu x k j) (heta : ∀ x i j, eta x i j = -theta x j i)
    (hcon : EMConstitutive eps eta theta nu E B D H) (hmax : MaxwellEqs D B E H Je Jm)
    (hE : ∀ x l, Differentiable ℝ (fun t => E x t l))
    (hH : ∀ x k, Differentiable ℝ (fun t => H x t k)) :
    (∀ x t j, B x t j = ∑ l, zetaEM (mu x) (theta x) j l * E x t l + ∑ k, mu x j k * H x t k) ∧
    (∀ x t i, D x t i = ∑ l, epsO (eps x) (eta x) (mu x) (theta x) i l * E x t l +
        ∑ k, xiEM (eta x) (mu x) i k * H x t k) ∧
    (∀ x i l, epsO (eps x) (eta x) (mu x) (theta x) i l =
        epsO (eps x) (eta x) (mu x) (theta x) l i) ∧
    (∀ x l j, xiEM (eta x) (mu x) l j = zetaEM (mu x) (theta x) j l) ∧
    MaxwellEO (fun x => epsO (eps x) (eta x) (mu x) (theta x)) (fun x => xiEM (eta x) (mu x)) mu
      E H Je Jm := by sorry

end Arxiv1810_02867
