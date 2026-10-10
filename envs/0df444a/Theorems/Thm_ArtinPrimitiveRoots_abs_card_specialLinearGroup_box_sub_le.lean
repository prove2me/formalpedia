-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_abs_card_specialLinearGroup_box_sub_le
-- name    : ArtinPrimitiveRoots.abs_card_specialLinearGroup_box_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:23:48.875007+00:00
-- url     : https://prove2.me/theorems/cf9063b0-1e37-41c7-aae7-95fa1b9c2672
-- title:
--   [21] Lemma 3.3 — the g ∈ SL₂(ℤ) with (u/U, v/V, c/u) in a box and g ≡ g₀ mod S number UV·vol/(ζ(2)|SL₂(ℤ/S)|) + O(UV x^{−c})
-- statement:
--   For every $\delta > 0$ there is $c > 0$ such that for every $C$ there is $x_0$ with the following property. Take $x \ge x_0$, $U, V \ge x^\delta$, and $S \le \exp(C(\log x)^{0.98})$ squarefree. Take $g_0 \in SL_2(\mathbb Z/S)$ and sets $I_1 \subseteq [1, 16]$, $I_2 \subseteq [1, 2]$, $I_3 \subseteq [0, 1]$, each containing the open interval $(a_i, b_i)$ and contained in the closed one $[a_i, b_i]$.
--
--   Count the $g = \begin{pmatrix} u & c \\ v & d \end{pmatrix} \in SL_2(\mathbb Z)$ with $u/U \in I_1$, $v/V \in I_2$, $0 \le c < u$, $c/u \in I_3$ and $g \equiv g_0 \pmod S$. This count differs from $UV(b_1 - a_1)(b_2 - a_2)(b_3 - a_3)/(\zeta(2)\,|SL_2(\mathbb Z/S)|)$ by at most $UVx^{-c}$.
--
--   The statement uses only Mathlib.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 15, Lemma 3.3.
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 15, Lemma 3.3

import Mathlib

namespace ArtinPrimitiveRoots

open Real

theorem abs_card_specialLinearGroup_box_sub_le :
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ,
      x ^ δ ≤ U → x ^ δ ≤ V →
      ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ Real.exp (C * Real.log x ^ (0.98 : ℝ)) →
      ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
        0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
      ∀ I₁ I₂ I₃ : Set ℝ, Set.Ioo a₁ b₁ ⊆ I₁ → I₁ ⊆ Set.Icc a₁ b₁ →
        Set.Ioo a₂ b₂ ⊆ I₂ → I₂ ⊆ Set.Icc a₂ b₂ → Set.Ioo a₃ b₃ ⊆ I₃ → I₃ ⊆ Set.Icc a₃ b₃ →
      |(Nat.card {g : Matrix.SpecialLinearGroup (Fin 2) ℤ //
          (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
          (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀} : ℝ) -
        U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
        U * V * x ^ (-c) := by
  sorry

end ArtinPrimitiveRoots
