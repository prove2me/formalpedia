-- Prove2me | Theorems.Thm_ChoresEFX_lemma_3_1
-- name    : ChoresEFX.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:13.966203+00:00
-- url     : https://prove2.me/theorems/4b8b3339-6948-44c3-9fc3-60fa5487f3ab
-- title:
--   Lemma 3.1 — a full flow gives a capped-price structure with $1-(n-1)t/n\le E_i\le1+t/n$
-- statement:
--   Let $\hat C>0$, $0<t\le1/100$, $0<\beta<1$ and $m\beta>n$. Let $v>0$ be weights, $s$ a water level, and $f$ a feasible flow in the network (3) of value $n$. Put $p_g=s\,r_g(v)$, $q_g=\min\{p_g,\beta\}$, $w_{ig}=f_{ig}/q_g$ and $\gamma_i=\min_g\hat C_i(g)/p_g$. Then $(p,\gamma,w)$ is a capped-price structure, and for every agent $i$,
--
--   $$1-\frac{(n-1)t}{n}\le E_i\le1+\frac{t}{n}.$$
--
--   This is the certificate MFCP returns when it stops.
--
--   Differences from the source:
--   - generalization: the weights of a round of Algorithm 2 and a maximum flow → any positive weights and any feasible flow of value n; reason: weights in a run are positive and a maximum flow of value n is feasible, so the page's case is a special case
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → n ≥ 1 ([Nonempty ι]); reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma 3.1, p.8

import Mathlib
import Definitions.Def_ChoresEFX_IsMfcpOutput

namespace ChoresEFX

/-- **Lemma 3.1**, p.8.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

If the maximum-flow value is `F = n`, Algorithm 2 outputs a capped-price structure `(p, γ, w)` with
`1 − (n − 1)t/n ≤ E_i ≤ 1 + t/n` for all `i`.

**Formalization Note.** Stated for any positive weights and any feasible flow of value `n`, which covers
every round of every run: such a flow is automatically maximum, since the source capacities sum to `n`.
`p`, `γ`, `w` are as in Algorithm 2, line 7. -/
theorem lemma_3_1 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (C : ι → κ → ℝ) (hC : ∀ i g, 0 < C i g) (t β : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 100)
    (hβ : 0 < β) (hβ' : β < 1) (hmβ : (Fintype.card ι : ℝ) < (Fintype.card κ : ℝ) * β)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (s : ℝ) (hs : IsWaterLevel C β v s) (f : ι → κ → ℝ)
    (hf : IsFeasibleFlow C t β v s f) (hF : flowValue f = (Fintype.card ι : ℝ)) :
    IsCappedPriceStructure C t β (roundPrice C v s) (mpbRatio C (roundPrice C v s))
        (fun i g => f i g / capped β (roundPrice C v s) g) ∧
    ∀ i,
      1 - ((Fintype.card ι : ℝ) - 1) * t / (Fintype.card ι : ℝ) ≤
        cappedIncome β (roundPrice C v s) (fun i g => f i g / capped β (roundPrice C v s) g) i ∧
      cappedIncome β (roundPrice C v s) (fun i g => f i g / capped β (roundPrice C v s) g) i ≤
        1 + t / (Fintype.card ι : ℝ) := by sorry

end ChoresEFX
