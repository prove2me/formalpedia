-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_theorem_3_1
-- name    : CommThresholdPR.StrongConverse.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:27.532209+00:00
-- url     : https://prove2.me/theorems/5d63db6f-ef8e-4293-bc3f-251c8bcf97c7
-- title:
--   Theorem 3.1 — exponential strong converse with both explicit exponents
-- statement:
--   Let $g\subseteq X\times Y\times A\times B$ be a total relation on nonempty finite alphabets, let $\mu$ be any joint input law, and let $0\le R<\operatorname{IC}_{\mu}(g,0)$. Then $\operatorname{err}_{\mu}(R)>0$, and for every $n\ge1$ and every finite randomized binary protocol $\Pi_n$ of worst-case cost at most $nR$,
--   $$\Pr_{\mu^{\otimes n}}[\Pi_n\text{ succeeds on every coordinate}]\le2^{-n\kappa(R)}.$$
--   The exponent is positive and is exactly
--   $$\kappa(R)=2^{-28}\min\left\{\frac{\operatorname{err}_{\mu}(R)^3}{L_{\rm out}},\frac{\operatorname{err}_{\mu}(R)^4R^2}{(1+L_{\rm in})^4}\right\}\quad(R>0),$$
--   $$\kappa(0)=\frac{\eta^3}{128L_{\rm out}},\qquad\eta=1-\omega(g,\mu)=\operatorname{err}_{\mu}(0).$$
--   Here $L_{\rm in}=\log_2(|X||Y|)$ and $L_{\rm out}=\log_2(|A||B|)$. There is no full-support, deterministic-only, positive-rate or bounded-round restriction. The threshold assumption supplies positivity and the nonzero output logarithm; these are not extra hypotheses. This is the source's full explicit strong converse.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: operational infima on nonempty sets bounded below by zero → a guarded real infimum over the entire protocol type; reason: on the source domain input exchange and zero-message protocols ensure nonemptiness and finite information is nonnegative; the fallback is only outside that domain, with these facts left to solvers
--   - encoding: n independent input pairs and their coordinatewise relation → Fin n coordinate strings and the PMF product of the joint law; reason: the indexing is bijective and independence is only across coordinates, without forcing independence of X and Y
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Theorem 3.1, p. 9, (13)–(15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem theorem_3_1 (g : TotalRelation X Y A B) (μ : PMF (X × Y))
    (R : ℝ) (hR : 0 ≤ R) (hbelow : R < informationComplexity g μ 0) :
    0 < errorAtRate g μ R ∧ errorAtRate g μ 0 = gap g μ ∧
    gap g μ = 1 - gameValue g μ ∧ 0 < exponent g μ R ∧
    (0 < R → exponent g μ R = (2 : ℝ) ^ (-28 : ℤ) *
      min (errorAtRate g μ R ^ 3 / logOutput A B)
        (errorAtRate g μ R ^ 4 * R ^ 2 / (1 + logInput X Y) ^ 4)) ∧
    (R = 0 → exponent g μ R = gap g μ ^ 3 / (128 * logOutput A B)) ∧
    ∀ (n : ℕ), 0 < n →
      ∀ piN : Protocol (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B),
      (piN.cost : ℝ) ≤ n * R →
      1 - protocolError (repeated g n) (inputPower μ n) piN ≤
        (2 : ℝ) ^ (-(n : ℝ) * exponent g μ R) := by sorry

end CommThresholdPR.StrongConverse
