-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_theorem_4_5
-- name    : DynReinsDiv.Barriers.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:14.275628+00:00
-- url     : https://prove2.me/theorems/e5ac12f2-10dd-4c4c-b627-68c76540cd8d
-- title:
--   Theorem 4.5 — for discrete claims the reinsurance boundaries K_j are C¹, start at 0, and satisfy (4.12)–(4.15)
-- statement:
--   Let the claims have the discrete law $\mathbb P(Z_1=z_j)=p_j>0$, $j=1,\dots,N$, with $0<z_1<\dots<z_N$ and $\sum_j p_j=1$. Let $v$ be the solution of Theorem 3.1 for this law (with $0<\gamma<\mu_1$), in the variables $(x,\tau)$, let $\lambda>0$ be a root of $f$ (A.12), and let
--   $$K_j(\tau)=\inf\Bigl\{x>0: -\frac{v_{xx}}{v_x}(x,\tau)\le\frac1{z_j}\Bigr\}$$
--   be the $j$-th reinsurance boundary. Then:
--   1. every $K_j$ is continuously differentiable on $(0,T]$;
--   2. if $z_j\le 1/\lambda$, then $K_j(\tau)=0$ for all $\tau\in(0,T]$ (4.12);
--   3. if $z_j>1/\lambda$ and $z_j$ is the smallest atom above $1/\lambda$ (that is, $j=1$ or $z_{j-1}\le1/\lambda$), then for all $\tau\in(0,T]$
--   $$0<K_j(\tau)<\frac{z_j-1/\lambda}{2c}; \tag{4.13}$$
--   4. if $z_{j-1}>1/\lambda$, then for all $\tau\in(0,T]$
--   $$0<K_j(\tau)-K_{j-1}(\tau)<\frac{z_j-z_{j-1}}{2c}; \tag{4.14}$$
--   5. $K_j(\tau)\to0$ as $\tau\to0+$ for every $j$ (4.15).
--
--   The boundaries split the surplus–time space into the regions where claims $z_j,\dots,z_N$ are partly ceded; the theorem says they emanate from the origin, are ordered in $j$, and are separated by explicit gaps.
--
--   **Formalization Note** Atoms are indexed from $0$ (`Fin N`). The paper's index $i_0$, the first atom above $1/\lambda$, is replaced by the conditions in items 2–4, which also cover the case where every atom is at most $1/\lambda$. Continuous differentiability on $(0,T]$ is `ContDiffOn ℝ 1` on `Set.Ioc 0 T` (one-sided at $T$). The model's law is required to be the discrete law, so $v$ is the same object as in the lemmas.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, pp. 19–20, Theorem 4.5, (4.12)–(4.15)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries
import Definitions.Def_DynReinsDiv_Barriers_Discrete

namespace DynReinsDiv.Barriers

/-- Theorem 4.5 (arXiv:2008.00391v3, pp. 19–20). Let the claims follow the discrete law
`ℙ(Z₁ = z_j) = p_j`, `j : Fin N` (0-based), let `v` be the solution of Theorem 3.1 (second argument
`τ`), `λ > 0` a root of `f` (A.12), and `K_j(τ) = inf{x > 0 | −v_xx/v_x(x, τ) ≤ 1/z_j}`. Then
* every `K_j` is continuously differentiable on `(0, T]`;
* (4.12) `K_j ≡ 0` on `(0, T]` whenever `z_j ≤ 1/λ`;
* (4.13) for the first atom above `1/λ` (`z_j > 1/λ` and the previous atom, if any, is `≤ 1/λ`):
  `0 < K_j(τ) < (z_j − 1/λ)/(2c)`;
* (4.14) whenever `z_{j−1} > 1/λ`: `0 < K_j(τ) − K_{j−1}(τ) < (z_j − z_{j−1})/(2c)`;
* (4.15) `K_j(τ) → 0` as `τ → 0+`. -/
theorem theorem_4_5 (M : Model) {N : ℕ} (D : DiscreteClaims N) (hμ : M.μ = D.law)
    (v vx vxx vt : ℝ → ℝ → ℝ) (hv : M.IsTheorem31Solution v vx vxx vt)
    (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0) :
    (∀ j : Fin N, ContDiffOn ℝ 1 (Kinf vx vxx (D.z j)) (Set.Ioc 0 M.T)) ∧
    (∀ j : Fin N, D.z j ≤ 1 / lam →
      ∀ τ ∈ Set.Ioc 0 M.T, Kinf vx vxx (D.z j) τ = 0) ∧
    (∀ j : Fin N, 1 / lam < D.z j → (∀ i : Fin N, i.val + 1 = j.val → D.z i ≤ 1 / lam) →
      ∀ τ ∈ Set.Ioc 0 M.T, 0 < Kinf vx vxx (D.z j) τ ∧
        Kinf vx vxx (D.z j) τ < (D.z j - 1 / lam) / (2 * M.c)) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → 1 / lam < D.z i →
      ∀ τ ∈ Set.Ioc 0 M.T, 0 < Kinf vx vxx (D.z j) τ - Kinf vx vxx (D.z i) τ ∧
        Kinf vx vxx (D.z j) τ - Kinf vx vxx (D.z i) τ < (D.z j - D.z i) / (2 * M.c)) ∧
    (∀ j : Fin N, Filter.Tendsto (Kinf vx vxx (D.z j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by sorry

end DynReinsDiv.Barriers
