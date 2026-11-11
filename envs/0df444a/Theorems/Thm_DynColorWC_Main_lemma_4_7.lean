-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_4_7
-- name    : DynColorWC.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:20.431245+00:00
-- url     : https://prove2.me/theorems/6a7c6413-86f5-474d-a289-00f299c0d788
-- title:
--   Lemma 4.7 — a vertex outside V_ε is (ε²/8)Δ-sparse
-- statement:
--   Let $\varepsilon\in(0,1)$, $\Delta\ge2/\varepsilon$, and let $G$ have maximum degree at most $\Delta$. If $v\notin V_\varepsilon$, then $v$ is $(\varepsilon^2/8)\Delta$-sparse.
--
--   Differences from the source:
--
--   - encoding: graph of maximum degree at most Δ (standing assumption of §3–§4) → hypothesis ∀ v, G.degree v ≤ Δ on a finite vertex type; reason: the standing assumption made explicit
--   - encoding: v is z-sparse (Definition 3.1) → IsSparse Δ G v z: nbrEdges G v ≤ C(Δ,2) − z·Δ over ℝ; reason: Definition 3.1 verbatim; nbrEdges is the published DynBrooks count of edges inside N(v)
--   - encoding: ε-friends, F_ε(v), V_ε (Definition 4.6) → AreFriends, friendSet, Veps with the thresholds (1−ε)Δ as real inequalities; reason: Definition 4.6 verbatim
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 4.7, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_DynBrooks_Sparsity
import Definitions.Def_DynColorWC_Main_AlmostClique

namespace DynColorWC.Main

open Classical in
/-- **Lemma 4.7** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 18 (PDF 20)). For `ε ∈ (0, 1)` and `Δ ≥ 2/ε`, in a graph of maximum degree at most `Δ`, every
vertex `v ∉ V_ε` is `(ε²/8)Δ`-sparse. -/
theorem lemma_4_7 {V : Type} [Fintype V] [DecidableEq V] (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (Δ : ℕ) (hΔ : 2 / ε ≤ (Δ : ℝ)) (G : SimpleGraph V) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V)
    (hv : v ∉ Veps ε Δ G) :
    IsSparse Δ G v (ε ^ 2 / 8 * Δ) := by sorry

end DynColorWC.Main
