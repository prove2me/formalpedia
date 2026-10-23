-- Prove2me | Theorems.Thm_AssortOpt_HMF_proposition_2
-- name    : AssortOpt.HMF.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:13.960321+00:00
-- url     : https://prove2.me/theorems/19832c10-02ae-40cb-9e2f-ed417fcecc66
-- title:
--   Proposition 2, p. 11 — f(S) = max_ℓ ∑_{j∈S∩ℓ} x_j(ℓ) is an increasing set function with x_{ℓ_k}(ℓ) = f(ℓ_{1:k}) − f(ℓ_{1:k−1}) and REV[f] = REV[x]
-- statement:
--   Let $\mathcal L, p$ be a list distribution with prices $r_j \ge 0$, and let $x$ be an IC mechanism. Define
--   $$f(S) = \max_{\ell \in \mathcal L} \sum_{j \in S \cap \ell} x_j(\ell), \qquad S \subseteq N. \qquad (7)$$
--   Then:
--   1. $f : 2^N \to [0,1]$ is an increasing set function;
--   2. for every $\ell \in \mathcal L$ and $k = 1, \dots, |\ell|$,
--   $$x_{\ell_k}(\ell) = f(\ell_{1:k}) - f(\ell_{1:k-1}); \qquad (8)$$
--   3. $\mathsf{REV}[f] = \mathsf{REV}[x]$;
--   4. therefore $\mathsf{OPT}^x \le \mathsf{OPT}^f$: some increasing set function has revenue at least $\mathsf{REV}[x]$.
--
--   $f(S)$ is the largest probability with which the buyer could obtain an item of $S$. The proposition is the second step of the relaxation chain $\mathsf{OPT}^S \le \mathsf{OPT}^x \le \mathsf{OPT}^f \le \mathsf{OPT}^\phi$, and shows that an IC mechanism can be run sequentially down the buyer's list.
--
--   **Formalization Note** $f$ is given as a hypothesis: for every $S$, $f(S)$ is the greatest element of $\{\sum_{j \in S \cap \ell} x_j(\ell) : \ell \in \mathcal L\}$. The support is finite and nonempty, so exactly one such $f$ exists. (8) is written 0-based: position $k+1$ of $\ell$ is `ℓ.get k`, and $\ell_{1:k+1}$ is `ℓ.take (k+1)`.
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: the definition (7) of $f$ → a hypothesis that $f(S)$ is the greatest value of $\ell \mapsto \sum_{j \in S\cap\ell} x_j(\ell)$ over $\mathcal L$, for every $S$; reason: the support is nonempty and finite, so this pins $f$ to (7).
--   - encoding: $k = 1,\dots,|\ell|$ in (8) → `k : Fin ℓ.length` with $\ell_{k+1}$, $\ell_{1:k+1}$, $\ell_{1:k}$; reason: 0-based indexing.
--   - encoding: $\mathsf{OPT}^x \le \mathsf{OPT}^f$ → some increasing $g$ has $\mathsf{REV}[x] \le \mathsf{REV}[g]$; reason: the optimal values are not named; same inequality.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 11, Proposition 2 (7)–(8)

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem proposition_2 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (x : List (Fin n) → Fin n → ℝ) (hx : IsIC D x) (f : Finset (Fin n) → ℝ)
    (hf : ∀ S : Finset (Fin n),
      IsGreatest ((fun ℓ => ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j) '' (D.supp : Set (List (Fin n)))) (f S)) :
    IsIncreasingSetFn f ∧
    (∀ ℓ ∈ D.supp, ∀ k : Fin ℓ.length,
      x ℓ (ℓ.get k) = f (ℓ.take (k + 1)).toFinset - f (ℓ.take k).toFinset) ∧
    revSetFn D r f = revMech D r x ∧
    (∃ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g ∧ revMech D r x ≤ revSetFn D r g) := by sorry

end AssortOpt.HMF
