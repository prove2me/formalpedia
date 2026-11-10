-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_5_7
-- name    : AlmostLinSubsetSum.Main.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:28:57.190053+00:00
-- url     : https://prove2.me/theorems/1a1c7d28-aca6-4299-89a7-37fe699b1661
-- title:
--   Lemma 5.7 — heavy items selected by a solution: $|X|\le2d\tau$ and bounded projections on every normal
-- statement:
--   **Lemma 5.7** (p. 25). Let $y\in T'_p$ be a target. Let $X$ be the set of indices of heavy items selected by a solution of $y$. Then
--   $$|X|\le2d\tau\ (21),\qquad \sum_{i\in X}|g_j\cdot v'_i|\le2(d+1)\ \text{(zonotope normals) }(22),\qquad \sum_{i\in X}|g_j\cdot v'_i|\le|X|/\tau\le2d\ \text{(window normals) }(23).$$
--
--   Setting of §5.2 as hypotheses: items $v_0,\dots,v_{n-1}\in\mathbb Z^d$ and $Z=\sum_i[0,v_i]$; an integer $\tau\ge1$; normals $g_0,\dots,g_{d-1}\in\mathbb R^d$, the zonotope normals indexed by a set $J_z$ and the window normals (the others) satisfying $|g_j\cdot v_i|\le1/\tau$ for all $i$ (18); a selection $\bar x$ maximizing $\sum_{j\in J_z}g_j\cdot V\bar x$ over all selections; $v'_i=(1-2\bar x_i)v_i$; an original target $t$ with $0\le h_Z(g_j)-g_j\cdot t\le2$ for every zonotope normal (17), and $y=t-V\bar x$; a solution $Y$ with $\sum_{i\in Y}v'_i=y$; item $i$ is heavy if $|g_j\cdot v'_i|>2/\tau$ for some $j$, and $X=Y\cap\{\text{heavy}\}$. Then (21), (22) for every $j\in J_z$, and both inequalities of (23) for every $j\notin J_z$.
--
--   Differences from the source:
--   - generalization: the normals g_1..g_d of D_p from Lemma 5.4 (normalized, independent, after the change of basis of Lemma 5.6), classified by (14)/(15), and targets y ∈ T'_p → arbitrary g_j ∈ ℝ^d with an arbitrary index set J_z of zonotope normals, (18) for the others, and any target y = t − V x̄ with t satisfying (17); reason: the proof uses only (17), (18) and the maximality of x̄; the paper's normals and targets satisfy them
--   - encoding: selection vectors x̄ ∈ {0,1}^n, items indexed 1..n, a solution of y as a set of items → x̄ and the solution Y as Finsets of Fin n (0-based); v'_i = reanchor x̄ v i; reason: a selection vector is the indicator of a subset
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 5.7, p. 25 (setting pp. 22–24)

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

open Classical in
/-- **Lemma 5.7** (Chen, Mao, Zhang 2026, p. 25). Let `y ∈ T'_p` be a target. Let `X` be the
set of indices of heavy items selected by a solution of `y`. Then `|X| ≤ 2dτ` (21),
`Σ_{i∈X} |g_j · v'_i| ≤ 2(d + 1)` for zonotope normals (22), and
`Σ_{i∈X} |g_j · v'_i| ≤ |X|/τ ≤ 2d` for window normals (23).

Setting of §5.2 as hypotheses: items `v_0, …, v_{n−1} ∈ ℤ^d`, `Z = Σ_i [0, v_i]`; an integer
scale `τ ≥ 1`; normals `g_0, …, g_{d−1} ∈ ℝ^d`, of which those indexed by `Jz` are the
zonotope normals and the others window normals with `|g_j · v_i| ≤ 1/τ` (18); `x̄ ⊆ {0..n−1}`
maximizes `Σ_{j∈Jz} g_j · V x̄` over all selections; `v'_i = (1 − 2x̄_i) v_i`; the target
`y ∈ T'_p` is `t − V x̄` for an original target `t` with `0 ≤ h_Z(g_j) − g_j · t ≤ 2` for every
zonotope normal (17); `Y` is a solution (`Σ_{i∈Y} v'_i = y`); item `i` is heavy if
`|g_j · v'_i| > 2/τ` for some `j`; `X = Y ∩ {heavy}`. -/
theorem lemma_5_7 {d n : ℕ} (v : Fin n → Fin d → ℤ) (τ : ℕ) (hτ : 1 ≤ τ)
    (g : Fin d → Fin d → ℝ) (Jz : Finset (Fin d))
    (hwin : ∀ j, j ∉ Jz → ∀ i, |g j ⬝ᵥ toReal (v i)| ≤ 1 / (τ : ℝ))
    (xbar : Finset (Fin n))
    (hxbar : ∀ x : Finset (Fin n),
      ∑ j ∈ Jz, g j ⬝ᵥ toReal (∑ i ∈ x, v i) ≤ ∑ j ∈ Jz, g j ⬝ᵥ toReal (∑ i ∈ xbar, v i))
    (t : Fin d → ℤ)
    (ht : ∀ j ∈ Jz,
      0 ≤ supportFn (zonotope Finset.univ (fun i => toReal (v i))) (g j) - g j ⬝ᵥ toReal t ∧
      supportFn (zonotope Finset.univ (fun i => toReal (v i))) (g j) - g j ⬝ᵥ toReal t ≤ 2)
    (Y : Finset (Fin n))
    (hY : ∑ i ∈ Y, reanchor xbar v i = t - ∑ i ∈ xbar, v i) :
    ((Y.filter (fun i => ∃ j, 2 / (τ : ℝ) < |g j ⬝ᵥ toReal (reanchor xbar v i)|)).card : ℝ)
        ≤ 2 * d * τ ∧
    (∀ j ∈ Jz,
      ∑ i ∈ Y.filter (fun i => ∃ j, 2 / (τ : ℝ) < |g j ⬝ᵥ toReal (reanchor xbar v i)|),
        |g j ⬝ᵥ toReal (reanchor xbar v i)| ≤ 2 * (d + 1)) ∧
    (∀ j, j ∉ Jz →
      ∑ i ∈ Y.filter (fun i => ∃ j, 2 / (τ : ℝ) < |g j ⬝ᵥ toReal (reanchor xbar v i)|),
        |g j ⬝ᵥ toReal (reanchor xbar v i)| ≤
        ((Y.filter (fun i => ∃ j, 2 / (τ : ℝ) < |g j ⬝ᵥ toReal (reanchor xbar v i)|)).card : ℝ)
          / τ ∧
      ((Y.filter (fun i => ∃ j, 2 / (τ : ℝ) < |g j ⬝ᵥ toReal (reanchor xbar v i)|)).card : ℝ)
          / τ ≤ 2 * d) := by sorry

end AlmostLinSubsetSum.Main
