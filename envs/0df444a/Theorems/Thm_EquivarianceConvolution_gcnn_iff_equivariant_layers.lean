-- Prove2me | Theorems.Thm_EquivarianceConvolution_gcnn_iff_equivariant_layers
-- name    : EquivarianceConvolution.gcnn_iff_equivariant_layers
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:03:08.076007+00:00
-- url     : https://prove2.me/theorems/a1c7904e-f852-444e-a40f-ac2867fdd70a
-- title:
--   Theorem 1 (as proved): G-CNNs are exactly the networks with equivariant linear layers
-- statement:
--   Let $G$ be a finite group and let $\mathcal N$ be an $(L+1)$-layer feed-forward network whose $\ell$-th index set is $\mathcal X_\ell=G/H_\ell$ for subgroups $H_\ell\le G$. Its activations lie in $\mathbb C^{d_\ell}$, its layers are linear maps $\phi_\ell:L_{\mathbb C^{d_{\ell-1}}}(G/H_{\ell-1})\to L_{\mathbb C^{d_\ell}}(G/H_\ell)$, and its pointwise nonlinearities $\sigma_\ell$ are arbitrary. Then:
--
--   1. if $\mathcal N$ is a $G$-CNN, then $\mathcal N$ is $G$-equivariant;
--   2. $\mathcal N$ is a $G$-CNN, i.e. every $\phi_\ell$ is a generalized convolution $\phi_\ell(f)=f*\chi_\ell$ with a filter $\chi_\ell$ on $H_{\ell-1}\backslash G/H_\ell$, **if and only if** every linear map $\phi_\ell$, $1\le\ell\le L$, is $G$-equivariant:
--
--   $$\phi_\ell(\mathbb T^{\ell-1}_gf)=\mathbb T^\ell_g\,\phi_\ell(f)\qquad\text{for all }g\in G,\ f\in L_{\mathbb C^{d_{\ell-1}}}(G/H_{\ell-1}).$$
--
--   This is the paper's main theorem, that convolutional structure is necessary and sufficient for equivariance, in the form its proof establishes.
--
--   **Formalization Note** The printed Theorem 1 asserts that $\mathcal N$ is $G$-equivariant (Definition 3) if and only if it is a $G$-CNN. Its "only if" direction is false. Equivariance of the activations does not force the linear maps to be equivariant when a nonlinearity is not injective, or when earlier layers do not reach every function. For example, take $G=\mathbb Z/2$, $H_\ell=\{e\}$, $L=2$, $\sigma_\ell=\mathrm{id}$, $\phi_1=0$ and $\phi_2(f)(x)=f(0)$. Every activation of layers 1 and 2 is $0$, so the network is equivariant, but $\phi_2$ is not equivariant and therefore not a convolution. The proof in Appendix E assumes that each $\phi_\ell$ is equivariant ("this is equivalent to asserting that $\phi_\ell$ is equivariant") and shows that each $\phi_\ell$ is then a convolution. The statement above is what the two proofs establish. The group is finite (see the definitions), and the activation spaces are $\mathbb C^{d_\ell}$, as in Definition 7.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Section 5, Theorem 1 and Definition 5, p. 6; proofs on p. 7 and in Appendix E, pp. 12-14

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem gcnn_iff_equivariant_layers {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) :
    (IsGCNN H L N → IsEquivariantNet G L N) ∧
      (IsGCNN H L N ↔ ∀ l < L, IsEquivariantMap G ⇑(N.phi l)) := by sorry

end EquivarianceConvolution
