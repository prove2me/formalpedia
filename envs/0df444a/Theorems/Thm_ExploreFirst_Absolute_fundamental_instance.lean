-- Prove2me | Theorems.Thm_ExploreFirst_Absolute_fundamental_instance
-- name    : ExploreFirst.Absolute.fundamental_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:19.392515+00:00
-- url     : https://prove2.me/theorems/9416c10a-8e03-4e0d-9e5a-ad32995b7111
-- title:
--   Theorem 2 proof — the pull-count instance of (6)
-- statement:
--   Consider two $K$-armed bandit problems $\underline\nu$ and $\underline\nu'$ whose arm laws have finite expectations and that differ only in arm $a$, any strategy $\psi$, and an integer $T\ge1$. For $p=\mathbb E_{\underline\nu}[N_{\psi,a}(T)]/T$ and $q=\mathbb E_{\underline\nu'}[N_{\psi,a}(T)]/T$, the fundamental inequality gives
--   $$\mathrm{kl}(p,q)\le\mathbb E_{\underline\nu}[N_{\psi,a}(T)]\,\mathrm{KL}(\nu_a,\nu'_a).$$
--
--   This is the page 11 application of inequality (6) with the random variable $N_{\psi,a}(T)/T$.
--
--   **Formalization Note** Both divergences are extended nonnegative reals, retaining infinite values. The count is bounded by $T$, so its expectation is an ordinary finite real number. The integrability hypotheses record the paper's standing definition of a bandit problem (§1.1).
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 11, first display of the proof of Theorem 2; (6), p. 6

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

namespace ExploreFirst.Absolute

/-- The instance of (6) used in the proof of Theorem 2, p. 11. -/
theorem fundamental_instance {K : ℕ} (π : BanditAlgorithm.BanditPolicy K)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (a : Fin K)
    (hνmean : ∀ k : Fin K, MeasureTheory.Integrable id (ν.P k))
    (hν'mean : ∀ k : Fin K, MeasureTheory.Integrable id (ν'.P k))
    (hother : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k)
    (T : ℕ) (hT : 1 ≤ T) :
    ExploreFirst.FundIneq.klBer (ExploreFirst.FundIneq.expPulls ν π T a / T) (ExploreFirst.FundIneq.expPulls ν' π T a / T) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) *
        InformationTheory.klDiv (ν.P a) (ν'.P a) := by sorry

end ExploreFirst.Absolute
