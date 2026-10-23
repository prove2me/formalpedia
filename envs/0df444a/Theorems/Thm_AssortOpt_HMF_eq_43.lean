-- Prove2me | Theorems.Thm_AssortOpt_HMF_eq_43
-- name    : AssortOpt.HMF.eq_43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:16.559719+00:00
-- url     : https://prove2.me/theorems/0bb7e39c-743e-4f70-9e39-36499abf76a1
-- title:
--   (43), proof of Theorem 2, p. 45 — REV[φ] − REV[S] rewritten as a sum over lists ℓ of p(ℓ) ∑_{k<κ^S(ℓ)} r^S(ℓ_{1:k}) times the stopping indicator
-- statement:
--   Let $\mathcal L, p$ be a list distribution with prices $r_j \ge 0$, let $\phi$ be a monotone stopping policy, and let $S$ be a set of items on which $\phi$ always stops ($\phi_j \equiv 1$ for $j \in S$). Let $\kappa^S(\ell)$ be the minimum $k$ with $\ell_k \in S$, and $\kappa^S(\ell) = |\ell| + 1$ if $\ell \cap S = \emptyset$. Then
--   $$\begin{aligned}\mathsf{REV}[\phi] - \mathsf{REV}[S] &= \sum_{\rho : \rho \cap S = \emptyset} r^S(\rho) \Big(\sum_{\ell : \ell_{1:|\rho|} = \rho} p(\ell)\Big) \phi_{\rho_{\mathrm{end}}}(\rho_{\mathrm{pre}}) \prod_{k=1}^{|\rho|-1} \big(1 - \phi_{\rho_k}(\rho_{1:k-1})\big) \\ &= \sum_{\ell \in \mathcal L} p(\ell) \sum_{k < \kappa^S(\ell)} r^S(\ell_{1:k})\, \phi_{\ell_k}(\ell_{1:k-1}) \prod_{k'=1}^{k-1} \big(1 - \phi_{\ell_{k'}}(\ell_{1:k'-1})\big). \end{aligned} \qquad (43)$$
--
--   The identity re-expresses Lemma 1 path by path: along each list, $\phi$'s advantage over $S$ is the adjusted price of the position where it stops before reaching $S$. The proof of Theorem 2 uses it to compare the revenue of a policy before and after one stopping decision is switched on.
--
--   **Formalization Note** $\kappa^S(\ell) - 1$ is the 0-based `ℓ.findIdx (· ∈ S)` (which equals $|\ell|$ when $\ell \cap S = \emptyset$), so the inner sum runs over `k ∈ range (findIdx)` with prefix `ℓ.take (k+1)`. The factor $\phi_{\ell_k}(\ell_{1:k-1}) \prod_{k' < k}(1 - \phi_{\ell_{k'}}(\ell_{1:k'-1}))$ is the bracket of (10) at $\rho = \ell_{1:k}$, `stopInd φ (ℓ.take (k+1))`. The outer sum on the first line runs over the nonempty realizable prefixes disjoint from $S$.
--
--   Differences from the source:
--   - generalization: $S$ = the set of $j$ for which $\phi_j$ is the all-1 function (proof of Theorem 2, p. 43) → any $S$ contained in that set; reason: the identity holds for every such $S$, and the page's $S$ is one of them.
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: $\kappa^S(\ell)$ and $k < \kappa^S(\ell)$ (1-based) → `ℓ.findIdx (· ∈ S)` and 0-based $k$ with prefix `ℓ.take (k+1)`; reason: 0-based indexing.
--   - encoding: the sum over prefixes $\rho$ with $\rho \cap S = \emptyset$ → the sum over nonempty realizable prefixes disjoint from $S$; reason: other prefixes have zero weight, and $r^S$ is defined only for realizable prefixes.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 45, display (43) in the proof of Theorem 2 (§E.2)

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem eq_43 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (φ : Policy n) (hφ : IsMonotonePolicy φ) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) :
    revPolicy D r φ - revAssort D r S =
      ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * (∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ) * stopInd φ ρ ∧
    revPolicy D r φ - revAssort D r S =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (ℓ.findIdx (fun i => decide (i ∈ S))),
        adjPrice D r S (ℓ.take (k + 1)) * stopInd φ (ℓ.take (k + 1)) := by sorry

end AssortOpt.HMF
