-- Prove2me | Theorems.Thm_DetCCHard_lemma_8_2
-- name    : DetCCHard.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:26.377547+00:00
-- url     : https://prove2.me/theorems/9fcd8b6e-039e-4cb7-8c6e-238b5e1fa557
-- title:
--   Lemma 8.2 — nesting exactly 8192-wise independent lists preserves exact independence
-- statement:
--   Let an inner indexed list on $Z^{q_{\rm in}}$ be exactly 8192-wise independent with marginal $\mu_Z$. Let an outer list on $q_{\rm out}$-tuples of inner labels be exactly 8192-wise independent with the inner label weights as marginal. Then the decoded coordinates, indexed by pairs in $[q_{\rm out}] \times [q_{\rm in}]$, are exactly 8192-wise independent with marginal $\mu_Z$. If the outer-list label has product weights with the tuple of labels from finitely many other lists, fixing those other labels at any joint value of positive weight leaves the outer-label weights, and hence the conclusion above, unchanged.
--
--   The lemma certifies the nested lists $\mathcal S_g$, $\mathcal J_g$ of the explicit construction.
--
--   **Formalization Note** The decoded list has the outer labels and weights and decodes $\ell$ to $(i, j) \mapsto z_{\rm in}(z_{\rm out}(\ell)_i)_j$. Fixing the other labels at $o_0$ gives outer weights $\ell \mapsto \nu_{\rm out}(\ell)\nu_O(o_0) / \sum_{\ell'} \nu_{\rm out}(\ell')\nu_O(o_0)$.
--
--   Differences from the source:
--   - generalization: the tuple of labels from finitely many other lists, with their product weights → any type O of joint values with any weights ν_O, fixed at o₀ with ν_O(o₀) > 0; reason: the joint labels of finitely many lists with product weights are a special case
--   - generalization: prescribed normalized (positive, §4.2) weights μ_Z on the alphabet Z → any μ_Z : Z → ℚ with which the inner list is exactly 8192-wise independent; reason: for q_in ≥ 1 exact independence forces μ_Z to be normalized and nonnegative (for q_in = 0 both conclusions are about the empty coordinate set), so positive μ_Z is a special case
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 8.2, p.35

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_TupleList

namespace DetCCHard

/-- **Lemma 8.2 (nested lists)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Lemma 8.2, p.35). Let an inner indexed list on `Z^{q_in}` be exactly 8192-wise
independent with marginal `μ_Z`. Let an outer list on `q_out`-tuples of inner labels be exactly
8192-wise independent with the inner label weights as marginal. Then the decoded coordinates,
indexed by pairs in `[q_out] × [q_in]`, are exactly 8192-wise independent with marginal `μ_Z`. If
the outer-list label has product weights with the tuple of labels from finitely many other lists,
fixing those other labels at any joint value of positive weight leaves the outer-label weights,
and hence the conclusion above, unchanged.

**Formalization Note** The decoded list has the outer labels and weights and decodes `ℓ` to
`(i, j) ↦ z_in(z_out(ℓ)_i)_j`. The other lists are represented by one finite type `O` of joint
values with any weights `ν_O` (the product of finitely many lists' weights is a special case);
the joint weight of `(ℓ, o)` is `ν_out(ℓ) ν_O(o)`, and fixing `o = o₀` with `ν_O(o₀) > 0` gives the
conditional weights `ℓ ↦ ν_out(ℓ) ν_O(o₀) / ∑_{ℓ'} ν_out(ℓ') ν_O(o₀)` on outer labels. -/
theorem lemma_8_2 {Z : Type} {q_in q_out : ℕ} (μZ : Z → ℚ) (Tin : TupleList Z (Fin q_in))
    (hin : ExactlyIndep Tin 8192 μZ) (Tout : TupleList Tin.L (Fin q_out))
    (hout : ExactlyIndep Tout 8192 Tin.ν) :
    ExactlyIndepW Tout.ν (fun ℓ (p : Fin q_out × Fin q_in) => Tin.z (Tout.z ℓ p.1) p.2) 8192 μZ ∧
    ∀ (O : Type) (νO : O → ℚ) (o₀ : O), 0 < νO o₀ →
      (∀ ℓ, Tout.ν ℓ * νO o₀ / (∑ ℓ', Tout.ν ℓ' * νO o₀) = Tout.ν ℓ) ∧
      ExactlyIndepW (fun ℓ => Tout.ν ℓ * νO o₀ / (∑ ℓ', Tout.ν ℓ' * νO o₀))
        (fun ℓ (p : Fin q_out × Fin q_in) => Tin.z (Tout.z ℓ p.1) p.2) 8192 μZ := by sorry

end DetCCHard
