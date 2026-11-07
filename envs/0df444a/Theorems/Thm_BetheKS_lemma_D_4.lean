-- Prove2me | Theorems.Thm_BetheKS_lemma_D_4
-- name    : BetheKS.lemma_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:15.854666+00:00
-- url     : https://prove2.me/theorems/87a50166-e294-4a65-9f7b-b72e1521dcd9
-- title:
--   Lemma D.4 — $|V^{(L,M)}(u)|+|[(H+\delta I)V^{(L,M)}](u)|\le C_L|B_{L+2}(G,u)|^{L+2}$
-- statement:
--   Let $G$ be any graph with vertex labeling $\sigma:V(G)\to[r]$, $t\ge\sqrt d>1$, $\delta>0$. For each fixed $L$ there is $C_L<\infty$, independent of $M$, such that
--   $$
--   |V^{(L,M)}(u)|+\big|[(H(t,G)+\delta I)V^{(L,M)}](u)\big|\le C_L\,|B_{L+2}(G,u)|^{L+2}.
--   $$
--   This polynomial bound supplies the growth condition of Lemma E.1 and the domination in Lemma D.7.
--
--   **Formalization Note** $C_L$ may depend on $t,\delta,\phi,L$ and is uniform over all locally finite labelled graphs, vertices and $M$.
--
--   Differences from the source:
--
--   - generalization: δ = δ(μ_i) and the fixed planted direction ϕ_i (App. D) → every δ > 0 and every ϕ : [r] → ℝ; reason: the statement and its proof use neither the value of δ nor the eigenfunction property
--   - encoding: any graph (finite or infinite) → any locally finite SimpleGraph on any type; reason: the paper's degrees deg(u) are finite
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma D.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_BetheKS_vertexFieldGraph

set_option autoImplicit false

namespace BetheKS

/-- **Lemma D.4** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.21
(PDF p.22): let `G` be any graph with vertex labeling `σ : V(G) → [r]`. For each fixed `L` there is
`C_L < ∞`, independent of `M`, such that
`|V^{(L,M)}(u)| + |[(H(t,G) + δI)V^{(L,M)}](u)| ≤ C_L |B_{L+2}(G, u)|^{L+2}`.

Standing assumptions (§3, App. D): `t ≥ √d > 1`, `δ > 0`, `X = ϕ ∘ σ`.

**Formalization Note.** `C_L` may depend on `t, δ, ϕ, L`, and is uniform over all locally finite
labelled graphs, vertices `u` and `M`. The statement is for every `δ > 0` and every `ϕ`. -/
theorem lemma_D_4 {r : ℕ} (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ)
    (ϕ : Fin r → ℝ) (L : ℕ) :
    ∃ C : ℝ, ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
      (σ : V → Fin r) (u : V) (M : ℕ),
      |vfIter G σ ϕ 1 t δ L M u| +
          |bhApply G t (vfIter G σ ϕ 1 t δ L M) u + δ * vfIter G σ ϕ 1 t δ L M u| ≤
        C * (Nat.card (ball G u (L + 2)) : ℝ) ^ (L + 2) := by sorry

end BetheKS
