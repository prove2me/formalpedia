-- Prove2me | Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
-- name    : AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/52289db9-a15c-5f24-8a8f-59a0a3a37c3a
-- title:
--   Compactness of the centre-cut Siegel set under height caps
-- statement:
--   Let $F$ be a number field, write $\mathcal{O}_F$ for its ring of integers and consider $\mathrm{GL}_2$ of the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`. Let $c, u, d_1, d_2, C$ be real numbers and assume only $0 < c$ and $0 < d_1$. For $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and an infinite place $w$ of $F$, let $g_w \in \mathrm{GL}_2(F_w)$ denote the image of $g$ under projection to the archimedean part followed by evaluation at $w$, and set $\mathrm{rowNormSq}(m) = \|m_{10}\|^2 + \|m_{11}\|^2$, $\mathrm{localHeight}(m) = \|\det m\| / \mathrm{rowNormSq}(m)$ and $\mathrm{xWindowSq}(m) = \mathrm{topNormSq}(m)/\mathrm{rowNormSq}(m) - \mathrm{localHeight}(m)^2$. The theorem asserts that the set of those $g$ such that the finite part `glFin (𝓞 F) F g` lies in the subgroup `finiteIntegralGL2 (𝓞 F) F` (the full-level subgroup `finiteLevelZero (𝓞 F) F ⊤`), and such that for every infinite place $w$ one has $c \le \mathrm{localHeight}(g_w)$, $\mathrm{xWindowSq}(g_w) \le u^2$ and $\|\det g_w\| \in [d_1, d_2]$, intersected with the set of $g$ satisfying $\mathrm{localHeight}(g_w) \le C$ at every infinite place $w$, is compact.
--
--   This is the compactness of a boxed block of a Siegel domain in adelic $\mathrm{GL}_2$, in the shape used by reduction theory: the Siegel conditions (integral finite part, height floor, window bound, two-sided determinant cut) together with an arbitrary per-place cap $C$ on the local heights cut out a compact set. It underlies the construction of compact covers of Siegel sets ([`AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le`](thm.html#AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le)) and the finiteness and approximation statements for centre-cut Siegel sets that are built on top of it; the cap $C$ is kept free, rather than tied to $c$, because balancing heights across several infinite places requires it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) := by sorry
