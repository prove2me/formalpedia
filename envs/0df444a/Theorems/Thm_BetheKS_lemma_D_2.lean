-- Prove2me | Theorems.Thm_BetheKS_lemma_D_2
-- name    : BetheKS.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:50.300893+00:00
-- url     : https://prove2.me/theorems/7bd54753-8f44-4a5d-b389-d825cd8f6c10
-- title:
--   Lemma D.2 — $V^{(L,M)}(u)$ and its residual are determined by $B_{M+L+2}(G,u)$
-- statement:
--   Let $G$ be any graph with vertex labeling $\sigma:V(G)\to[r]$, $t\ge\sqrt d>1$, $\delta>0$. For fixed integers $L,M\ge0$, the values
--   $$
--   V^{(L,M)}(u)\qquad\text{and}\qquad\big[(H(t,G)+\delta I)V^{(L,M)}\big](u)
--   $$
--   are determined by the ball $B_{M+L+2}(G,u)$. This locality makes Lemma E.1 applicable to the finite-graph fields.
--
--   **Formalization Note** "Determined by the ball": the values agree for any two locally finite labelled graphs whose rooted labelled balls of radius $M+L+2$ are isomorphic.
--
--   Differences from the source:
--
--   - generalization: δ = δ(μ_i) and the fixed planted direction ϕ_i (App. D) → every δ > 0 and every ϕ : [r] → ℝ; reason: the statement and its proof use neither the value of δ nor the eigenfunction property
--   - encoding: any graph (finite or infinite) → any locally finite SimpleGraph on any type; reason: the paper's degrees deg(u) are finite
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma D.2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_BetheKS_vertexFieldGraph

set_option autoImplicit false

namespace BetheKS

/-- **Lemma D.2** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.20
(PDF p.21): let `G` be any graph with vertex labeling `σ : V(G) → [r]`. For fixed integers
`L, M ≥ 0`, the values `V^{(L,M)}(u)` and `[(H(t,G) + δI)V^{(L,M)}](u)` are determined by the ball
`B_{M+L+2}(G, u)`.

Standing assumptions (§3, App. D): `t ≥ √d > 1`, `δ > 0`, `X = ϕ ∘ σ`.

**Formalization Note.** "Determined by the ball": the values agree for any two locally finite
labelled graphs whose rooted labelled balls of radius `M + L + 2` are isomorphic. The statement is for
every `δ > 0` and every `ϕ : [r] → ℝ` (the paper's are `δ = δ(µᵢ)` and `ϕ = ϕᵢ`). -/
theorem lemma_D_2 {r : ℕ} (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ)
    (ϕ : Fin r → ℝ) {V V' : Type} [DecidableEq V] [DecidableEq V']
    (G : SimpleGraph V) [G.LocallyFinite] (G' : SimpleGraph V') [G'.LocallyFinite]
    (σ : V → Fin r) (σ' : V' → Fin r) (u : V) (u' : V') (L M : ℕ)
    (hball : BallIso ({ V := V, G := G, lab := σ, root := u } : RLGraph r)
      ({ V := V', G := G', lab := σ', root := u' } : RLGraph r) (M + L + 2)) :
    vfIter G σ ϕ 1 t δ L M u = vfIter G' σ' ϕ 1 t δ L M u' ∧
    bhApply G t (vfIter G σ ϕ 1 t δ L M) u + δ * vfIter G σ ϕ 1 t δ L M u =
      bhApply G' t (vfIter G' σ' ϕ 1 t δ L M) u' + δ * vfIter G' σ' ϕ 1 t δ L M u' := by sorry

end BetheKS
