-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_5_1
-- name    : ExactParallelSampling.QuasiUniform.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:54.211547+00:00
-- url     : https://prove2.me/theorems/55b9700e-f6ad-46f1-9da4-57e28cf8be97
-- title:
--   Lemma 5.1 — Efron–Stein weights are integer multiples of 1/lcm(1,…,r) and encode all circuits of B + x
-- statement:
--   Fix a quasi-uniform $\mu$, an independent set $B$ and $x\notin B$ with $r=s_x\ge2$, and write $s(Z)=s_Z(x)$. Let $Y$ be uniform on $\Omega_B$. Let $p_B(Y)-u=\sum_{A\subseteq B}f_A(Y_A)$ be the Efron–Stein decomposition of the vector-valued function $p_B-u$, where $p_Z(y)$ is the conditional law of $X_x$ given $X_Z=y_Z$ and $u$ is uniform on $\Omega_x$. Let $w_A=\mathbb E\|f_A(Y_A)\|^2$ and $L=\mathrm{lcm}(1,\dots,r)$.
--
--   (a) For every $Z\subseteq B$, $\sum_{\emptyset\ne A\subseteq Z}w_A=1/s(Z)-1/r$.
--
--   (b) Every $w_A$ is a non-negative integer multiple of $1/L$. Hence the family $H=\{A\ne\emptyset:w_A>0\}$ has at most $L(1-1/r)$ members.
--
--   (c) For $Z\subseteq B$, the set $Z+x$ is dependent iff some $A\in H$ satisfies $A\subseteq Z$. The circuits contained in $B+x$ are the sets $A+x$ with $A$ an inclusion-minimal member of $H$.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: the Efron–Stein decomposition p_B(Y) − u = Σ_A f_A(Y_A) [ES81] → f_A := Σ_{T⊆A} (−1)^{|A∖T|} E[p_B(Y) − u | Y_T] for Y uniform on Ω_B (esComponent); reason: this is the closed form of the Efron–Stein components of a function of a random vector with independent coordinates; Y is uniform on the product Ω_B because B is independent
--   - encoding: vectors in ℝ^{Ω_x} and their squared norms → functions α → ℝ vanishing off Ω_x, with Σ_a v(a)²; reason: the coordinates outside Ω_x are 0
--   - encoding: w_A is a non-negative integer multiple of 1/L → ∃ k : ℕ, w_A = k / L (for every A ⊆ B, including A = ∅); reason: the natural-number multiplier carries non-negativity; w_∅ = 0
--   - encoding: the circuits contained in B + x are the sets A + x with A minimal in H → C ∈ circuitsIn (IsIndep p) (insert x B) ↔ ∃ A ∈ H minimal in H with C = insert x A; reason: literal rendering
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 5.1, p. 24–25; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 5.1 (Efron–Stein integrality)**, Shen, Li, Shi and Li (2026), pp. 24–25. Fix a
quasi-uniform `μ`, an independent set `B` and `x ∉ B` with `r = s_x ≥ 2`; `s(Z) = s_Z(x)`. Let `Y`
be uniform on `Ω_B`, let `p_B(Y) − u = ∑_{A ⊆ B} f_A(Y_A)` be the Efron–Stein decomposition of the
vector-valued function `p_B − u`, `w_A = E‖f_A(Y_A)‖²` and `L = lcm(1, …, r)`.
(a) For every `Z ⊆ B`, `∑_{∅ ≠ A ⊆ Z} w_A = 1/s(Z) − 1/r`.
(b) Every `w_A` is a non-negative integer multiple of `1/L`; hence `H = {A ≠ ∅ : w_A > 0}` has at
most `L(1 − 1/r)` members.
(c) For `Z ⊆ B`, `Z + x` is dependent iff some `A ∈ H` satisfies `A ⊆ Z`. The circuits contained
in `B + x` are the sets `A + x` with `A` an inclusion-minimal member of `H`. -/
theorem lemma_5_1 {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (B : Finset E) (hB : IsIndep p B) (x : E) (hx : x ∉ B)
    (hr : 2 ≤ s p x) :
    -- (a)
    (∀ Z ⊆ B, ∑ A ∈ Z.powerset.filter (fun A => A ≠ ∅), esWeight p B x A = esF p x Z) ∧
    -- (b)
    (∀ A ⊆ B, ∃ k : ℕ, esWeight p B x A = (k : ℝ) / (lcmUpTo (s p x) : ℝ)) ∧
    ((esH p B x).card : ℝ) ≤ (lcmUpTo (s p x) : ℝ) * (1 - 1 / (s p x : ℝ)) ∧
    -- (c)
    (∀ Z ⊆ B, ¬ IsIndep p (insert x Z) ↔ ∃ A ∈ esH p B x, A ⊆ Z) ∧
    (∀ C : Finset E, C ∈ circuitsIn (IsIndep p) (insert x B) ↔
      ∃ A ∈ esH p B x, (∀ A' ∈ esH p B x, A' ⊆ A → A' = A) ∧ C = insert x A) := by sorry

end ExactParallelSampling.QuasiUniform
