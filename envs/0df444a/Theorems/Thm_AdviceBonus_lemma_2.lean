-- Prove2me | Theorems.Thm_AdviceBonus_lemma_2
-- name    : AdviceBonus.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:41.209737+00:00
-- url     : https://prove2.me/theorems/c5c64005-c1b0-445e-93d7-bd8dcc8e371c
-- title:
--   Lemma 2 — the equilibrium bonus $b=4G(\bar q^A_2)/g(\bar q^A_2)\cdot w$ (14) (corrected: equilibria with $b<w$)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $p,c\in\mathbb R$ and $w>0$. If $(f,b)$ is a symmetric equilibrium compensation scheme with $f>0$ and $0<b<w$, then the bonus satisfies
--   $$
--   b=\frac{4G(\bar q^A_2)}{g(\bar q^A_2)}\,w, \qquad(14)
--   $$
--   where $\bar q^A_2$ is the cutoff (2) at the equilibrium profile.
--
--   Since $\bar q^A_2=\frac12-\frac b{2w}$ at a symmetric scheme, (14) becomes the fixed-point equation (15) for the cutoff (Lemma 3).
--
--   Differences from the source:
--   - correction: a symmetric equilibrium with f > 0 and b > 0 → a symmetric equilibrium with f > 0 and 0 < b < w (advice to the second customer informative: q̄A2, q̄B2 ∈ (0, 1)); reason: the printed statement is false: for g ≡ 1, p − c = 1, w = 1/5 the scheme (f, b) = (3/5, 3/5) is a symmetric equilibrium (q̄A2 = 0, q̄B2 = 1; in the lock-in region firm A's profit is (1/2 + (T − 9/5)/(2/5))(2 − T) in T = 2f′ + b′, maximal at T = 9/5 with value 1/10, and a fine grid over X finds no better deviation for either firm), yet (14) would give b = 4G(0)/g(0)·w = 0; the proof (p.32) starts from the interior cutoffs 1/2 ∓ b/(2w), and §3 restricts to informative advice (p.10)
--   - reading: "a symmetric equilibrium" → a symmetric pure Nash equilibrium of the compensation stage at the given price p, strategy set {f ≥ 0, 2f + b ≥ 0}, profits (6); reason: §4 takes p_n = p as given (p.16), and p.8 gives the limited-liability strategy set
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3)
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
--   - generalization: the model's standing assumption (1) on v_h, v_l and c → not assumed; p and c arbitrary reals; reason: §4 takes p as given and (1) only restricts the customer side; the statement specializes to the source's under (1)
--   - encoding: advisor payoffs include w_l → w_l dropped; reason: it cancels from every cutoff
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Lemma 2, eq. (14), p.17; proof in Appendix A, pp.32–34

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_AdviceBonus_Equilibrium

namespace AdviceBonus

/-- **Lemma 2**, eq. (14), p.17 (Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). In a symmetric
equilibrium with `f_n = f > 0` and `b_n = b > 0` in which
the advice to the second customer is informative (`b < w`, so that `q̄^A_2, q̄^B_2 ∈ (0, 1)`), the bonus satisfies
`b = 4 G(q̄^A_2)/g(q̄^A_2) · w`, where `q̄^A_2` is the cutoff (2) at the equilibrium profile.

**Formalization Note** (corrected) The hypothesis `b < w` is not printed in the lemma. Without it the
statement is false: for `g ≡ 1`, `p − c = 1`, `w = 1/5`, the scheme `(f, b) = (3/5, 3/5)` is a
symmetric equilibrium (both second cutoffs clamp, `q̄^A_2 = 0`, `q̄^B_2 = 1`, and no deviation in
`X` beats the profit `1/10`), while (14) gives `b = 0`. The paper's proof (p.32) starts from the
interior cutoffs `1/2 ∓ b/(2w)`, i.e. `b < w`, and §3 restricts attention to informative advice
(p.10). -/
theorem lemma_2 (D : Dist) (p c w : ℝ) (hw : 0 < w) (f b : ℝ)
    (heq : IsSymEq D p c w (f, b)) (hf : 0 < f) (hb : 0 < b) (hbw : b < w) :
    b = 4 * D.G (q2A w (f, b) (f, b)) / D.g (q2A w (f, b) (f, b)) * w := by sorry

end AdviceBonus
