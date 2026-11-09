-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_lemma_3_6
-- name    : CollectiveTreeExploration.Async.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:38.984208+00:00
-- url     : https://prove2.me/theorems/56c85385-7e4f-41c4-86d4-2220ca1ccfdd
-- title:
--   Lemma 3.6 — electrical representation of the elongation
-- statement:
--   Let $k\ge2$, $T$ a game tree with fractional minimizer $y$, and $l$ a non-root leaf elongated at unit rate. Then for every leaf $\ell$,
--   $$\sum_{u\in\ell\to r}\frac{\rho_u}{y_u}\,\dot y_u=\frac{\dot\Phi/k-y_l^\varepsilon\,\mathbf 1_{\{\ell=l\}}}{\varepsilon}.$$
--   Therefore $\dot y$ is the current in the resistive network on $T$ in which each edge $(p_u,u)$, $u\ne r$, has resistance $r_u=\rho_u/y_u$ and the leaf voltages are
--   $$V_\ell=0\ (\ell\ne l),\qquad V_l=y_l^\varepsilon/\varepsilon:\tag{8}$$
--   it satisfies Kirchhoff's and Ohm's laws for these voltages, and it is the only current of this network. In this network the effective resistance between $u$ and $L_u$ is
--   $$R_u=\frac{h_u}{y_u}.$$
--
--   This turns the evolution of the minimizer into an electrical computation.
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: ẏ can be interpreted as the current obtained in the resistive network → ẏ satisfies Kirchhoff's law and Ohm's law for a potential with the voltages (8) at the leaves, and every current of that network equals ẏ on every edge; effective resistance defined by Thomson's principle (least energy of a unit flow from u to L_u); reason: precise meaning of "the current" and of the effective resistance
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Lemma 3.6, p.9; proof p.10; electrical networks, §2.1, p.5

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Lemma 3.6** (electrical representation, p.9). In the unit-rate elongation of the leaf `l`,
for every leaf `ℓ`: `∑_{u ∈ ℓ → r} (ρ_u / y_u) ẏ_u = (Φ̇/k − y_l^ε 1{ℓ = l}) / ε`. Therefore `ẏ`
is the current in the resistive network on `T` with resistances `r_u = ρ_u / y_u` and leaf
voltages `V_ℓ = 0` (`ℓ ≠ l`), `V_l = y_l^ε / ε` (8): it satisfies Kirchhoff's and Ohm's laws, and
it is the only current of that network. In this network the effective resistance between `u` and
`L_u` is `R_u = h_u / y_u`. -/
theorem lemma_3_6 (k : ℕ) (hk : 2 ≤ k) (T : WTree) (hT : T.IsGameTree) (l : ℕ)
    (hl : l ∈ T.leaves) (hlr : l ≠ T.root) :
    (∀ ℓ ∈ T.leaves, ∑ u ∈ T.pathVerts ℓ T.root,
        T.rho k u / T.mass (T.fracMin k) u * T.mass (T.ydot k l) u =
      (T.phiDot k l / k - (if ℓ = l then T.fracMin k l ^ eps k else 0)) / eps k) ∧
    T.IsCurrent (T.netRes k) (T.netVolt k l) (T.mass (T.ydot k l)) ∧
    (∀ i : ℕ → ℝ, T.IsCurrent (T.netRes k) (T.netVolt k l) i →
      ∀ u ∈ T.V, u ≠ T.root → i u = T.mass (T.ydot k l) u) ∧
    ∀ u ∈ T.V, T.effRes (T.netRes k) u = T.hgt k u / T.mass (T.fracMin k) u := by sorry

end CollectiveTreeExploration.Async
