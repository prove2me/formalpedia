-- Prove2me | Theorems.Thm_BetheKS_lemma_3_2
-- name    : BetheKS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:48.692171+00:00
-- url     : https://prove2.me/theorems/0fb0c773-4cfc-459d-994b-28a8c9cae123
-- title:
--   Lemma 3.2 — $0=(\Gamma_u^{(v)})^{(0)}\le(\Gamma_u^{(v)})^{(1)}\le\cdots\le c_\delta$
-- statement:
--   Let $G$ be any graph, finite or infinite, $t\ge\sqrt d>1$, $\delta>0$ and $c_\delta=t/(t^2+\delta)$. For every directed edge $(u,v)$,
--   $$
--   0=(\Gamma_u^{(v)})^{(0)}\le(\Gamma_u^{(v)})^{(1)}\le\cdots\le c_\delta .
--   $$
--   So the cavity weights $\Gamma_u^{(v)}$ of Definition 3.3 exist and satisfy $0\le\Gamma_u^{(v)}\le c_\delta$.
--
--   Differences from the source:
--
--   - encoding: any graph (finite or infinite) → any locally finite SimpleGraph on any type; reason: the paper's degrees deg(u) are finite
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma 3.2, p.7 (PDF p.8); proof in App. A, p.13

import Mathlib
import Definitions.Def_BetheKS_cavityIter

set_option autoImplicit false

namespace BetheKS

/-- **Lemma 3.2** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.7 (PDF p.8):
for every directed edge `(u, v)`, `0 = (Γ_u^{(v)})^{(0)} ≤ (Γ_u^{(v)})^{(1)} ≤ ⋯ ≤ c_δ`.

Standing assumptions of §3 (p.6): `G` is any graph, finite or infinite; `t ≥ √d > 1`, `δ > 0`,
`c_δ = t/(t² + δ)`.

**Formalization Note.** Graphs are locally finite `SimpleGraph`s on any type. -/
theorem lemma_3_2 (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ)
    {V : Type} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite] (u v : V) (huv : G.Adj u v) :
    cavIter G t δ 0 u v = 0 ∧ Monotone (fun M => cavIter G t δ M u v) ∧
      ∀ M, cavIter G t δ M u v ≤ cDelta t δ := by sorry

end BetheKS
