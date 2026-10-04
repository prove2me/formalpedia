-- Prove2me | Theorems.Thm_BartlettNN_Margin_log_Ninf_squash_lt
-- name    : BartlettNN.Margin.log_Ninf_squash_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:06:18.902215+00:00
-- url     : https://prove2.me/theorems/5e409b85-1387-4bad-a50b-02b77b4344e7
-- title:
--   Proof of Theorem 2 — log₂ N∞(π_γ(H), γ/2, 2m) < 1 + d log₂(34em/d) log₂(578m)
-- statement:
--   Let $H$ be a class of real functions on $X$, $\gamma>0$, and let $d\ge 1$ be an integer with $\operatorname{fat}_{\pi_\gamma(H)}(\gamma/16)\le d$ and $d\le 2m$. If
--   $$
--   m\ \ge\ d\log_2(34em/d)+1,
--   $$
--   then $\mathcal N_\infty(\pi_\gamma(H),\gamma/2,2m)$ is finite and
--   $$
--   \log_2\mathcal N_\infty(\pi_\gamma(H),\gamma/2,2m)\ <\ 1+d\log_2(34em/d)\log_2(578m).
--   $$
--   This is Theorem 5 applied with $n=2m$ and $b=17$ to the quantized class, and is the covering-number estimate that, substituted into Lemma 4, yields Theorem 2.
--
--   **Formalization Note** The hypothesis $d\le 2m$ is not printed; it is the range ($d\le n$) of the estimate $\sum_{i=0}^d\binom ni b^i\le (ebn/d)^d$ behind the constant $34em/d$, and it is needed: for $d$ close to $34em$ the right-hand side is close to $1$ while the proviso holds, and the claim fails for rich classes. Under the proviso, $d\le 34m$ already forces $d\le 2m$, and for $d>2m$ the paper calls the result trivial. The paper's $d=\operatorname{fat}_H(\gamma/16)$; the hypothesis is phrased with $\operatorname{fat}_{\pi_\gamma(H)}(\gamma/16)$, and the milestone $\operatorname{fat}_{\pi_\gamma(H)}(\gamma/16)\le\operatorname{fat}_H(\gamma/16)$ bridges the two. $e$ is `Real.exp 1`.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, proof of Theorem 2, display after 'Applying Theorem 5 with n = 2m and b = 17 gives'

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Proof of Theorem 2** (Bartlett 1998, p. 528, "Applying Theorem 5 with n = 2m and b = 17").
Let `γ > 0`, `d ≥ 1` with `fat_{π_γ(H)}(γ/16) ≤ d`, and `d ≤ 2m`. If
`m ≥ d log₂(34em/d) + 1`, then `N∞(π_γ(H), γ/2, 2m)` is finite and
`log₂ N∞(π_γ(H), γ/2, 2m) < 1 + d log₂(34em/d) log₂(578m)`. The hypothesis `d ≤ 2m` is the range
of the binomial estimate the derivation uses; the printed sentence leaves it implicit. -/
theorem log_Ninf_squash_lt {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) (m d : ℕ)
    (hd : 1 ≤ d) (hd2m : d ≤ 2 * m) (hfat : fat (squashClass γ H) (γ / 16) ≤ d)
    (hm : (d : ℝ) * Real.logb 2 (34 * Real.exp 1 * m / d) + 1 ≤ m) :
    Ninf (squashClass γ H) (γ / 2) (2 * m) < ⊤ ∧
      Real.logb 2 ((Ninf (squashClass γ H) (γ / 2) (2 * m)).toNat : ℝ) <
        1 + d * Real.logb 2 (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) := by sorry

end BartlettNN.Margin
