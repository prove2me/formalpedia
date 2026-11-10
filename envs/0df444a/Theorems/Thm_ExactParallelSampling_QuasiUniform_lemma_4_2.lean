-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_4_2
-- name    : ExactParallelSampling.QuasiUniform.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:52.254562+00:00
-- url     : https://prove2.me/theorems/29ec6c8e-a4c8-4a38-9422-476a69eecd28
-- title:
--   Lemma 4.2 — deferral of certified coordinates preserves the law and strictly lowers their support sizes
-- statement:
--   Let $\mu$ be quasi-uniform on $\Sigma^E$, and let $R\subseteq E$ be a set such that every $x\in R$ has a certificate: an independent set $T_x\subseteq E\setminus R$ such that $T_x+x$ is dependent. Then:
--
--   (a) If $y$ is distributed as $X_{E\setminus R}$ and, given $y$, $w$ is distributed as the conditional law of $X_R$ given $X_{E\setminus R}=y$, then $(y,w)$ is distributed as $\mu$. In the Lean, for every $x$, $\Pr[X_{E\setminus R}=x_{E\setminus R}]\cdot\Pr[X_R=x_R\mid X_{E\setminus R}=x_{E\setminus R}]=\mu(x)$.
--
--   (b) The law of $X_{E\setminus R}$ is quasi-uniform, and its independent sets are the independent sets of $\mu$ contained in $E\setminus R$.
--
--   (c) For every $y\in\Omega_{E\setminus R}$, the conditional law of $X_R$ given $X_{E\setminus R}=y$ is quasi-uniform, and in it every $x\in R$ takes $s_{E\setminus R}(x)\le s_x-1$ values.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: (y, w) is distributed as μ → for every x : E → α, marg p (E∖R) (x restricted) · condLaw p (E∖R) (x restricted) (x on R) = p x; reason: the left side is the probability that the two-stage draw yields (x_{E∖R}, x_R); at an inconsistent pinning both sides are 0
--   - encoding: independent sets of the law of X_{E∖R}, subsets of E ∖ R → F : Finset ↥(E∖R), compared with its image in E; reason: subsets of E ∖ R are finsets of the subtype
--   - encoding: the conditional law of X_R given X_{E∖R} = y → condLaw p (E∖R) y on the subtype {j // j ∉ E∖R}, whose elements are exactly those of R; reason: subtype encoding of R
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 4.2, p. 21; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 4.2 (Deferral)**, Shen, Li, Shi and Li (2026), p. 21. Let `μ` be quasi-uniform on `Σ^E`
and let `R ⊆ E` be such that every `x ∈ R` has a certificate: an independent `T_x ⊆ E ∖ R` with
`T_x + x` dependent. Then:
(a) if `y` is distributed as `X_{E∖R}` and, given `y`, `w` as the conditional law of `X_R` given
`X_{E∖R} = y`, then `(y, w)` is distributed as `μ`;
(b) the law of `X_{E∖R}` is quasi-uniform, and its independent sets are the independent sets of
`μ` contained in `E ∖ R`;
(c) for every `y ∈ Ω_{E∖R}`, the conditional law of `X_R` given `X_{E∖R} = y` is quasi-uniform, and
in it every `x ∈ R` takes `s_{E∖R}(x) ≤ s_x − 1` values. -/
theorem lemma_4_2 {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (R : Finset E)
    (hcert : ∀ x ∈ R, ∃ T : Finset E, T ⊆ Finset.univ \ R ∧ IsIndep p T ∧
      ¬ IsIndep p (insert x T)) :
    -- (a)
    (∀ x : E → α,
      marg p (Finset.univ \ R) ((Finset.univ \ R).restrict x) *
        condLaw p (Finset.univ \ R) ((Finset.univ \ R).restrict x) (fun j => x j.1) = p x) ∧
    -- (b)
    (IsQuasiUniform (marg p (Finset.univ \ R)) ∧
      ∀ F : Finset ↥(Finset.univ \ R),
        IsIndep (marg p (Finset.univ \ R)) F ↔
          IsIndep p (F.map (Function.Embedding.subtype _))) ∧
    -- (c)
    (∀ y ∈ supp p (Finset.univ \ R), IsQuasiUniform (condLaw p (Finset.univ \ R) y) ∧
      ∀ x (hx : x ∈ R),
        (s (condLaw p (Finset.univ \ R) y) ⟨x, by simp [hx]⟩ : ℝ) =
            condSize p (Finset.univ \ R) x ∧
          condSize p (Finset.univ \ R) x ≤ (s p x : ℝ) - 1) := by sorry

end ExactParallelSampling.QuasiUniform
