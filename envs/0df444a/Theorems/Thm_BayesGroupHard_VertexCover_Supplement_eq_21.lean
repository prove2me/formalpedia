-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_eq_21
-- name    : BayesGroupHard.VertexCover.Supplement.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:46:17.205995+00:00
-- url     : https://prove2.me/theorems/c6333fb0-353d-4ce0-ab82-f11ea6a3cc86
-- title:
--   (21), p. 32 — φ_i,2 is the log-ratio of the likelihood sums over Σ; (0,1,…,1) ∈ Σ and its s_κ = 1 profiles are the exact covers
-- statement:
--   In the EXACT-COVER reduction network of an RXC3 instance $\hat{\mathcal G}_n$, let $s$ be a signal profile on which agent $i$ observes the history (19). Then:
--
--   1. agent $i$'s information set at time two consists exactly of the profiles $s'$ with $s'_i=s_i$ and $(s'_\kappa,s'_{\tau_1},\dots,s'_{\tau_n})\in\Sigma$;
--   2. her log-belief ratio at time two is
--   $$\phi_{i,2}=\log\frac{\sum_{(s_\kappa,s_\tau)\in\Sigma}(\bar p^\star)^{s_\kappa}(1-\bar p^\star)^{1-s_\kappa}\,\bar p^{\sum_j s_{\tau_j}}(1-\bar p)^{n-\sum_j s_{\tau_j}}}{\sum_{(s_\kappa,s_\tau)\in\Sigma}(\underline p^\star)^{s_\kappa}(1-\underline p^\star)^{1-s_\kappa}\,\underline p^{\sum_j s_{\tau_j}}(1-\underline p)^{n-\sum_j s_{\tau_j}}};$$
--   3. $(0,1,\dots,1)\in\Sigma$;
--   4. $(0,1,\dots,1)$ is the only element of $\Sigma$ with $s_\kappa=0$;
--   5. $(1,s_{\tau_1},\dots,s_{\tau_n})\in\Sigma$ if and only if the subsets $\tau_j$ with $s_{\tau_j}=1$ form an exact cover.
--
--   So the posterior of agent $i$ is determined by the exact covers of the instance, which is what makes it hard to compute.
--
--   **Formalization Note.** The two sums are `coreMass X true` and `coreMass X false`; the signals of the element agents and of $i$, being non-informative, cancel between numerator and denominator, which item 1 makes explicit.
--
--   Differences from the source:
--   - encoding: sums over (s_κ, s_τ1, …, s_τn) ∈ Σ → `coreMass` over `CoreProfile n`, together with the explicit information set of item 1; reason: the non-informative signals of the element agents and of i factor out of the posterior.
--   - encoding: agent i receives no private signal → a fair-coin signal of i, with s'_i = s_i in the information set; reason: a non-informative signal changes no posterior.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 32, definition of Σ, (21) and the characterisation of Σ below it

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

namespace BayesGroupHard.VertexCover.Supplement

open Finset

/-- (21), p. 32: on a signal profile realising the history (19), agent `i`'s information set at
time two consists of the profiles with her own signal whose informative part lies in `Σ`; her
log-belief ratio is the log of the ratio of the likelihood sums over `Σ`; `(0,1,…,1) ∈ Σ`, it is
the only profile of `Σ` with `s_κ = 0`, and the profiles of `Σ` with `s_κ = 1` are exactly the
exact covers. -/
theorem eq_21 {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool) (hs : Observed X s) :
    rInfo (xcNet X) 2 observer s =
      univ.filter (fun s' => s' observer = s observer ∧ project s' ∈ sigma X) ∧
    rLog (xcNet X) 2 observer s = Real.log (coreMass X true / coreMass X false) ∧
    baseProfile n ∈ sigma X ∧
    (∀ v : Fin n → Bool, (false, v) ∈ sigma X ↔ v = fun _ => true) ∧
    (∀ v : Fin n → Bool, (true, v) ∈ sigma X ↔ ExactCover X (selected (true, v))) := by sorry

end BayesGroupHard.VertexCover.Supplement
