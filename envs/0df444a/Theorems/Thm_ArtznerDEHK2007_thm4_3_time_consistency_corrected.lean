-- Prove2me | Theorems.Thm_ArtznerDEHK2007_thm4_3_time_consistency_corrected
-- name    : ArtznerDEHK2007.thm4_3_time_consistency_corrected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:34:38.256554+00:00
-- url     : https://prove2.me/theorems/0bbf934d-2ebc-4ca2-b578-d295fa7187d1
-- title:
--   Theorem 4.3 — stability $\iff$ time consistency for value processes ($\mathcal F_0$ trivial)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P_0)$ be a probability space with a filtration $(\mathcal F_n)$ whose initial σ-algebra $\mathcal F_0$ is $\mathbb P_0$-trivial, fix a horizon $N$, and let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$. For a bounded adapted process $X$ and a stopping time $\sigma\le N$ let $\Psi_\sigma(X)=\operatorname{ess\,inf}\{\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma] : \sigma\le\tau\le N,\ \mathbb Q\in\mathcal P^e\}$, and let $X^{\tau-}$ be $X$ frozen at $X_{\tau-1}$ from time $\tau$ on. Call $\mathcal P$ time consistent for value processes if for all value processes $X,Y$ and stopping times $\sigma\le\tau\le N$,
--
--   $$X^{\tau-}=Y^{\tau-}\ \text{and}\ \Psi_\tau(X)\le\Psi_\tau(Y)\ \Longrightarrow\ \Psi_\sigma(X)\le\Psi_\sigma(Y)\quad\text{a.s.}$$
--
--   Then $\mathcal P$ is stable under pasting if and only if it is time consistent for value processes.
--
--   This is Theorem 4.3 of Artzner, Delbaen, Eber, Heath and Ku, with the assumption that $\mathcal F_0$ is trivial, under which Theorem 4.2 is formalized as MultiperiodRisk.Bellman.stable_tfae; the paper derives it from Bellman's principle in Theorem 4.2.
--
--   **Formalization Note** Definitions and conventions ($X_{-1}=0$, stopping times bounded by $N$, a.s. equalities) are those of MultiperiodRisk.Bellman.stable_tfae.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007), doi:10.1007/s10479-006-0132-6; manuscript of Nov. 16, 2004, p. 13, Definition 4.1 and Theorem 4.3

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps

open MeasureTheory MultiperiodRisk.Bellman

theorem ArtznerDEHK2007.thm4_3_time_consistency_corrected {Ω : Type*} {m : MeasurableSpace Ω}
    (P₀ : Measure Ω) [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (hℱ₀ : ∀ s, MeasurableSet[ℱ 0] s → P₀ s = 0 ∨ P₀ s = 1)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    IsStable D ↔
      ∀ X Y : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X → IsValueProcess P₀ ℱ N Y →
        ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
          (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
          (∀ n ≤ N, preStop X τ n =ᵐ[P₀] preStop Y τ n) →
          Psi D X τ hτ.1 ≤ᵐ[P₀] Psi D Y τ hτ.1 →
          Psi D X σ hσ.1 ≤ᵐ[P₀] Psi D Y σ hσ.1 := by sorry
