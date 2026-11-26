-- Prove2me | Theorems.Thm_Arxiv2507_18491_reaction_exponentials_decay
-- name    : Arxiv2507_18491.reaction_exponentials_decay
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:59:40.149705+00:00
-- url     : https://prove2.me/theorems/30d59b7b-8d9a-4213-a6d8-bd51a275afd0
-- title:
--   Section 3.1: the $Z$-functions decay exponentially at the rate of the vertical transmission distance
-- statement:
--   Let the layered medium have interfaces $d_0>\dots>d_{L-1}$, frequency $\omega>0$, and $\varepsilon_j,\mu_j>0$. Let the height $z$ lie strictly inside layer $\ell$ and $z'$ strictly inside layer $\ell'$. Let $(\ast,\star)$ be a reaction field component whose case of (3.9) uses only existing interfaces. Let $D=|\hat z-\breve z|$ be its vertical transmission distance, the distance between the heights of the effective location $\hat\tau^{\ast\star}_{\ell\ell'}(\boldsymbol r)$ and of the equivalent polarization coordinate $\breve\tau^{\star}_{\ell\ell'}(\boldsymbol r')$. Then $D>0$ and
--   $$Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z')\sim e^{-k_\rho D}\qquad(k_\rho\to+\infty).$$
--   So every such $Z$-function decays exponentially, at the rate given by its vertical transmission distance.
--
--   **Formalization Note** "$\sim$" is asymptotic equivalence ($Z/e^{-k_\rho D}\to1$). The remark that this choice of $Z$-functions has the *minimal* transmission distance among the non-unique representations (Remark 3.1) is not formalized. The wave numbers are real (lossless layers).
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c003; Section 3.1, text after eq. (3.11) (with eqs. (3.9), (3.21), (3.22), (3.24)), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem reaction_exponentials_decay (omega : ℝ) (epsL muL : ℕ → ℝ) (homega : 0 < omega)
    (heps : ∀ j, 0 < epsL j) (hmu : ∀ j, 0 < muL j) (L : ℕ) (d : ℕ → ℝ)
    (hd : IsInterfaces L d) (l l' : ℕ) (a b : Dir) (hab : CompDefined L l l' a b)
    (z z' : ℝ) (hz : InLayer L d l z) (hz' : InLayer L d l' z') :
    0 < vertDist d l l' a b z z' ∧
    Asymptotics.IsEquivalent atTop
      (fun krho : ℝ => Zfun (waveNum omega epsL muL) d l l' a b krho z z')
      (fun krho : ℝ => ((Real.exp (-(krho * vertDist d l l' a b z z')) : ℝ) : ℂ)) := by sorry

end Arxiv2507_18491
