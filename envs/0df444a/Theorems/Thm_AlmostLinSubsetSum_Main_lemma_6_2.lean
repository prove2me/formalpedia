-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_6_2
-- name    : AlmostLinSubsetSum.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:02.602202+00:00
-- url     : https://prove2.me/theorems/d4dd55f9-ee42-4680-aad4-2cd2c6b5643c
-- title:
--   Lemma 6.2 — the pivot is deep in the projected core: $t_0+6\eta\tau\cdot Q\subseteq FJ$
-- statement:
--   **Lemma 6.2** (p. 28). A box around the pivot lies in $FJ$:
--   $$t_0+6\eta\tau\cdot Q\subseteq FJ\quad(27).$$
--
--   Setting as hypotheses: a box $Q=\prod_j[-q_j,q_j]$ with $q_j\ge1$; an integer $\tau\ge1$; $\eta>0$; integer items $v_i\in\mathbb Z^d$ indexed by disjoint finite sets $I_R$ and $I_G$, with $v_i\in Q$ for $i\in I_R$ and $|I_R|\le\eta\tau/2$ (from (8)); $u_i\in\mathbb Z^r$ and an integer matrix $F$ with $Fu_i=v_i$ for $i\in I_G$; $Z=\sum_{i\in I_R\cup I_G}[0,v_i]$, $J=\sum_{i\in I_G}[0,u_i]$; the pivot $t_0\in\mathbb Z^d$ is interior: $t_0+8\eta\tau\cdot Q\subseteq Z$.
--
--   Differences from the source:
--   - generalization: the prepared instance of §4 (Theorem 4.2's data, an interior target from Lemma 4.5) and the fixed small constant η of (3) → any data with v_i ∈ Q on I_R, |I_R| ≤ ητ/2, F u_i = v_i on I_G, t₀ + 8ητ·Q ⊆ Z, and any η > 0; reason: the proof uses only these facts; the paper's instance satisfies them
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 6.2, p. 28

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 6.2** (Chen, Mao, Zhang 2026, p. 28). A box around the pivot lies in `FJ`:
`t₀ + 6ητ · Q ⊆ FJ` (27).

Setting of §4 and §6 as hypotheses: a box `Q = ∏_j [−q_j, q_j]` with `q_j ≥ 1`; an integer
scale `τ ≥ 1`; `η > 0`; items `v_i ∈ ℤ^d` indexed by the disjoint sets `I_R` (reserve, with
`v_i ∈ Q` and `|I_R| ≤ ητ/2`, from (8)) and `I_G`; vectors `u_i ∈ ℤ^r` and an integer matrix
`F` with `F u_i = v_i` for `i ∈ I_G`; `Z = Σ_{i ∈ I_R ∪ I_G} [0, v_i]`,
`J = Σ_{i∈I_G} [0, u_i]`; the pivot `t₀` is interior: `t₀ + 8ητ · Q ⊆ Z`. -/
theorem lemma_6_2 {ι : Type*} [DecidableEq ι] {d r : ℕ} (q : Fin d → ℝ) (hq : ∀ j, 1 ≤ q j)
    (τ : ℕ) (hτ : 1 ≤ τ) (η : ℝ) (hη : 0 < η)
    (v : ι → Fin d → ℤ) (u : ι → Fin r → ℤ) (F : Matrix (Fin d) (Fin r) ℤ)
    (IR IG : Finset ι) (hdisj : Disjoint IR IG)
    (hFu : ∀ i ∈ IG, F.mulVec (u i) = v i)
    (hvR : ∀ i ∈ IR, toReal (v i) ∈ box q)
    (hR : (IR.card : ℝ) ≤ η * τ / 2)
    (t₀ : Fin d → ℤ)
    (hint : translate (toReal t₀) (dilate (8 * η * τ) (box q)) ⊆
      zonotope (IR ∪ IG) (fun i => toReal (v i))) :
    translate (toReal t₀) (dilate (6 * η * τ) (box q)) ⊆
      realMap F '' zonotope IG (fun i => toReal (u i)) := by sorry

end AlmostLinSubsetSum.Main
