-- Prove2me | Theorems.Thm_EquivarianceConvolution_gcnn_is_equivariant
-- name    : EquivarianceConvolution.gcnn_is_equivariant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:02:41.260676+00:00
-- url     : https://prove2.me/theorems/8ee30b0b-6676-4c75-a58d-98dd09c766e8
-- title:
--   Theorem 1 (forward direction): every G-CNN is G-equivariant
-- statement:
--   Let $G$ be a finite group and let $\mathcal N$ be an $(L+1)$-layer feed-forward network whose $\ell$-th index set is $G/H_\ell$ for subgroups $H_\ell\le G$, with activations in $\mathbb C^{d_\ell}$ and arbitrary pointwise nonlinearities. If $\mathcal N$ is a $G$-CNN, then it is $G$-equivariant: for every $g\in G$ and input $f_0$, replacing $f_0$ by $\mathbb T^0_gf_0$ replaces every activation $f_\ell$, $0\le\ell\le L$, by $\mathbb T^\ell_gf_\ell$. Here a $G$-CNN is one in which every linear map is $\phi_\ell(f)=f*\chi_\ell$ with a filter $\chi_\ell$ on $H_{\ell-1}\backslash G/H_\ell$.
--
--   This is the "if" direction of Theorem 1, proved on p. 7 of the paper.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Section 5, Theorem 1, p. 6; proof of the forward direction, p. 7

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem gcnn_is_equivariant {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) (hN : IsGCNN H L N) :
    IsEquivariantNet G L N := by sorry

end EquivarianceConvolution
