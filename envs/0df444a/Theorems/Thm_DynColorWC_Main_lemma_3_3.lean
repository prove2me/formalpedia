-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_3_3
-- name    : DynColorWC.Main.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:25.561521+00:00
-- url     : https://prove2.me/theorems/76db4c27-cd17-4fb0-b1ff-49b958556a75
-- title:
--   Lemma 3.3 — members of an ε-almost-clique C with z(C) ≥ 32/(δε²) are (δε²/100)·z(C)-sparse
-- statement:
--   Let $\varepsilon\in(0,1/75)$, $\delta\in(0,1)$, and let $G$ be a graph of maximum degree at most $\Delta$. Suppose $V_{sp},C_1,C_2,\dots$ is a vertex partition such that every vertex of $V_{sp}$ is $(\varepsilon^2\delta\Delta)$-sparse and each $C_i$ is an $\varepsilon$-almost-clique. Then every $v\in C_i$ with $z(C_i)\ge 32/(\delta\varepsilon^2)$ is $\frac{\delta\varepsilon^2}{100}z(C_i)$-sparse.
--
--   Differences from the source:
--
--   - encoding: graph of maximum degree at most Δ (standing assumption of §3–§4) → hypothesis ∀ v, G.degree v ≤ Δ on a finite vertex type; reason: the standing assumption made explicit
--   - encoding: v is z-sparse (Definition 3.1) → IsSparse Δ G v z: nbrEdges G v ≤ C(Δ,2) − z·Δ over ℝ; reason: Definition 3.1 verbatim; nbrEdges is the published DynBrooks count of edges inside N(v)
--   - encoding: vertex partition V_sp, C_1, …, C_r → a labelling cl : V → Option ℕ, V_sp = cl⁻¹(none), C_i = cl⁻¹(some i); reason: the same partitions; unused labels give empty sets, which are trivially ε-almost-cliques
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 3.3, p. 14 (PDF 16)

import Mathlib
import Definitions.Def_DynBrooks_Sparsity
import Definitions.Def_DynColorWC_Main_AlmostClique

namespace DynColorWC.Main

open Classical in
/-- **Lemma 3.3** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 14 (PDF 16)). Let `ε ∈ (0, 1/75)` and `δ ∈ (0, 1)`, and let `G` have maximum degree at most `Δ`.
Suppose `V_sp, C_1, C_2, …` is a vertex partition (`cl v = none` for `v ∈ V_sp`, `cl v = some i` for
`v ∈ C_i`) such that every vertex of `V_sp` is `(ε²·δΔ)`-sparse and each `C_i` is an
`ε`-almost-clique. Then every `v ∈ C_i` with `z(C_i) ≥ 32/(δε²)` is `(δε²/100)·z(C_i)`-sparse. -/
theorem lemma_3_3 {V : Type} [Fintype V] [DecidableEq V] (ε δ : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 75)
    (hδ : 0 < δ) (hδ' : δ < 1) (Δ : ℕ) (G : SimpleGraph V) (hdeg : ∀ v, G.degree v ≤ Δ)
    (cl : V → Option ℕ)
    (hsp : ∀ v, cl v = none → IsSparse Δ G v (ε ^ 2 * δ * Δ))
    (hcl : ∀ i, IsAlmostClique ε Δ G (Finset.univ.filter fun v => cl v = some i)) :
    ∀ (i : ℕ) (v : V), cl v = some i →
      32 / (δ * ε ^ 2) ≤ zC Δ G (Finset.univ.filter fun u => cl u = some i) →
      IsSparse Δ G v (δ * ε ^ 2 / 100 * zC Δ G (Finset.univ.filter fun u => cl u = some i)) := by sorry

end DynColorWC.Main
