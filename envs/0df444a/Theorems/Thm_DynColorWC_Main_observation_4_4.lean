-- Prove2me | Theorems.Thm_DynColorWC_Main_observation_4_4
-- name    : DynColorWC.Main.observation_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:45.049078+00:00
-- url     : https://prove2.me/theorems/ad916b88-d126-40a1-a51e-58eeb0ed0787
-- title:
--   Observation 4.4 — |z^τ₂(C) − z^τ₁(C)| ≤ 4X/Δ + 9Y for a cluster of size ≥ Δ/2 at both times
-- statement:
--   Let $G_0,G_1,\dots$ be graphs of maximum degree at most $\Delta$ evolving by single edge updates, and $C_0,C_1,\dots$ the successive vertex sets of a cluster. Let $\tau_1\le\tau_2$ be such that $|C_{\tau_1}|\ge\Delta/2$ and $|C_{\tau_2}|\ge\Delta/2$. If $X$ is the number of updates incident on $C$ over $[\tau_1,\tau_2]$ and $Y$ the recourse of $C$ over $[\tau_1,\tau_2]$, then
--   $$|z^{\tau_2}(C)-z^{\tau_1}(C)|\le 4X/\Delta+9Y.$$
--
--   Differences from the source:
--
--   - generalization: update times of the dynamic graph: each update inserts or deletes one edge → any sequence of graphs G_t of maximum degree ≤ Δ in which consecutive graphs differ in at most one edge, and any sequence of vertex sets C_t; reason: steps that change no edge only leave X unchanged; it specializes to the dynamic graph and a cluster with a fixed identifier
--   - reading: X, the number of updates incident on C over [τ₁, τ₂]; Y, the recourse of C over [τ₁, τ₂] → X = #{t ∈ (τ₁, τ₂] : the edge changed at t has an endpoint in C_{t−1}}; Y = Σ_{t ∈ (τ₁, τ₂]} |C_t ⊕ C_{t−1}|; reason: exactly the updates between the two times; counting fewer updates is the stronger reading, and the printed proof bounds the change of S this way
--   - encoding: z^τ(C) → zC Δ G_τ C_τ (§3.1 formula, with max{0, Δ − |C|}); reason: z(C) of §3.1 at time τ
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Observation 4.4, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_DynColorWC_Main_AlmostClique

namespace DynColorWC.Main

open Classical in
/-- **Observation 4.4** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 17 (PDF 19)). Let `G_0, G_1, …` be graphs on `V` of maximum degree at most `Δ`, consecutive ones
differing in at most one edge (one edge insertion or deletion per update), and let `C_0, C_1, …` be
vertex sets (a cluster with a fixed identifier, at each time). Let `τ₁ ≤ τ₂` with `|C_{τ₁}| ≥ Δ/2`
and `|C_{τ₂}| ≥ Δ/2`. Let `X` be the number of updates `t ∈ (τ₁, τ₂]` whose edge has an endpoint in
`C_{t−1}`, and `Y = Σ_{t ∈ (τ₁, τ₂]} |C_t ⊕ C_{t−1}|` the recourse of the cluster. Then
`|z^{τ₂}(C) − z^{τ₁}(C)| ≤ 4X/Δ + 9Y`, where `z^τ(C) = z(C_τ)` is computed in `G_τ`. -/
theorem observation_4_4 {V : Type} [Fintype V] [DecidableEq V] (Δ : ℕ)
    (G : ℕ → SimpleGraph V) (hdeg : ∀ t v, (G t).degree v ≤ Δ)
    (hstep : ∀ t, (symmDiff (G (t + 1)).edgeSet (G t).edgeSet).Subsingleton)
    (C : ℕ → Finset V) (τ₁ τ₂ : ℕ) (hτ : τ₁ ≤ τ₂)
    (h₁ : (Δ : ℝ) / 2 ≤ ((C τ₁).card : ℝ)) (h₂ : (Δ : ℝ) / 2 ≤ ((C τ₂).card : ℝ)) :
    let X : ℕ := ((Finset.Ioc τ₁ τ₂).filter fun t =>
        ∃ e ∈ symmDiff (G t).edgeSet (G (t - 1)).edgeSet, ∃ x ∈ e, x ∈ C (t - 1)).card
    let Y : ℕ := ∑ t ∈ Finset.Ioc τ₁ τ₂, (symmDiff (C t) (C (t - 1))).card
    |zC Δ (G τ₂) (C τ₂) - zC Δ (G τ₁) (C τ₁)| ≤ 4 * (X : ℝ) / Δ + 9 * (Y : ℝ) := by sorry

end DynColorWC.Main
