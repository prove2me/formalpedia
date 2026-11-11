-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_claim_5_4
-- name    : CaiFourierSparse.Learning.claim_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:20.028177+00:00
-- url     : https://prove2.me/theorems/97998069-0615-413a-81be-0b59a219e037
-- title:
--   Claim 5.4 — ApproxAccess samples from $p_\ell$, is unbiased, and has integrated variance $O(\log k)\|y\|^2/R$
-- statement:
--   In Algorithm 1 ($K=2^a\ge k$, $K=O(k)$), let $w\in W$ be a type of support $\ell$, $R\ge1$, and $y$ an observation with finite window energy. For every $u\in[-1,1)\setminus\frac{\mathbb Z}{2\ell}$, each sample $u_r$ of $\mathrm{ApproxAccess}(w,\ell,R,u)$ is a draw from $p_\ell$ on the fibre $\{(u+2a)/\ell\bmod2\}$, i.e. takes the fibre point $t$ with probability $p_\ell(t)/\sum_{t'}p_\ell(t')$, and the output satisfies $\mathbb E[\tilde z(u)]=\zeta_w(u)$. Moreover
--   $$\int_{-1}^1\mathbb E\big[|\tilde z(u)-\zeta_w(u)|^2\big]\,du\le C\,\frac{\log k}{R}\,\|y\|^2_{[-1,1]}.$$
--   For every bound $c$ on $K/k$ there is such a constant $C$.
--
--   Differences from the source:
--   - reading: K = O(k) (§5: 'ℓ could be as large as K = O(k)') → for every c ≥ 1 there is a constant C valid for all K ≤ c·k; reason: the section's standing K = O(k) with an unspecified ratio; quantifying over every ratio is the strongest reading
--   - encoding: u ∈ [−1,1) \ ℤ/(2ℓ) → u ∈ [−1,1) and u ≠ n/(2ℓ) for every integer n; reason: same set
--   - encoding: each u_r is a random sample from p_ℓ → the law of one round (roundLaw) equals Σ_{t in the fibre} (p_ℓ(t)/Σ_{t'} p_ℓ(t'))·δ_t; rounds are independent (product law); reason: the fibre has ℓ points; 'sample from p_ℓ' is p_ℓ restricted to them and normalized (p. 31)
--   - encoding: O(log k)/R → C·log k / R with C fixed before k, a, w, R, y; reason: the O-constant is universal for each ratio bound c
--   - encoding: the observation y = x + η → any y with a.e.-measurable restriction and finite window energy; reason: η is arbitrary, so y ranges over exactly these functions
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Claim 5.4, printed p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_ApproxAccess

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Claim 5.4 (printed p. 26, PDF p. 28). In Algorithm 1 (`K = 2^a ≥ k` with `K = O(k)`: for
every ratio bound `c`, `K ≤ c k`), for every type `w` of support `ℓ`, every `R ≥ 1`, every
observation `y` with finite window energy and every `u ∈ [-1,1) \ ℤ/(2ℓ)`: each sample `u_r` of
`ApproxAccess(w, ℓ, R, u)` is a draw from `p_ℓ` restricted to the fibre `{(u + 2a)/ℓ mod 2}`
(probability `p_ℓ(t)/∑_{t'} p_ℓ(t')`), and the output `z̃(u)` satisfies `E[z̃(u)] = ζ_w(u)`;
moreover `∫_{-1}^{1} E|z̃(u) - ζ_w(u)|² du ≤ C (log k / R) ‖y‖²_{[-1,1]}`. -/
theorem claim_5_4 :
    ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, 0 < C ∧
      ∀ (k a R : ℕ) (w : Option ℕ), 1 ≤ k → k ≤ 2 ^ a → (2 : ℝ) ^ a ≤ c * k →
        w ∈ haarTypes a → 1 ≤ R →
        ∀ y : ℝ → ℂ, AEStronglyMeasurable y (volume.restrict window) → wsq y < ⊤ →
          (∀ u ∈ Set.Ico (-1 : ℝ) 1, (∀ n : ℤ, u ≠ n / (2 * (typeLen a w : ℝ))) →
            roundLaw (typeLen a w) u =
                ∑ t ∈ fibre (typeLen a w) u,
                  ENNReal.ofReal (pEll (typeLen a w) t /
                    ∑ t' ∈ fibre (typeLen a w) u, pEll (typeLen a w) t') • Measure.dirac t ∧
              ∫ us, approxAccessOut a w y R us ∂(approxAccessLaw (typeLen a w) R u) =
                zeta a w y u) ∧
          ∫⁻ u in window, ∫⁻ us, ‖approxAccessOut a w y R us - zeta a w y u‖ₑ ^ 2
              ∂(approxAccessLaw (typeLen a w) R u) ≤
            ENNReal.ofReal (C * Real.log k / R) * wsq y := by sorry

end CaiFourierSparse.Learning
