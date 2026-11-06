-- Prove2me | Theorems.Thm_FewExperts_lemma_7_failure
-- name    : FewExperts.lemma_7_failure
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:12.336202+00:00
-- url     : https://prove2.me/theorems/59a1791a-0c41-4e41-8cf9-90285dff2fb5
-- title:
--   Lemma 7 — if $\mathcal A$ fails, it transitioned at a bad index or $\mathcal A'$ failed
-- statement:
--   Take HarvestGain$(\ell,\widetilde T,\mathcal B)$ with $\ell>0$, $\alpha\ell\ge1$, $1\le\widetilde T\le T$, a baseline predicting mixtures, gains in $[0,1]$, and any thresholds. Suppose the run fails, that is, it stops at a round $t$ with $G_t^{\mathcal A}<G_t^{\mathcal B}+\alpha\ell-16\sqrt{\widetilde T}$. Then it transitioned at some $(t^*,i^*,r^*)$, and one of the following holds:
--
--   1. $r^*$ is a bad index of $i^*$;
--   2. the recursive run $\mathcal A'=$ HarvestGain$(\ell,\widetilde T',\mathcal B')$ fails, with respect to its own baseline $\mathcal B'$ and horizon $\widetilde T'$.
--
--   With Lemma 6, this gives the failure bound of Proposition 2 (ii) by induction.
--
--   Differences from the source:
--   - encoding: B′ = two-expert Hedge "by Lemma 2" (rate left implicit); ties to "the first expert" → B′ = Hedge with rate √(ln 2/T̃′) on the streams of B and i*; ties broken towards the lowest index of Fin N; reason: the rate of Lemma 2's Hedge with n = 2 and horizon T̃′; "first" read as lowest index
--   - encoding: a baseline algorithm ℬ (randomness fixed, p.17) → the sequence b of ℬ's mixed predictions on the fixed gain sequence (probability vectors on rounds 1, …, T̃); reason: for fixed gains and fixed randomness a baseline is determined by its predictions; every realization is covered
--   - generalization: T and N sufficiently large (convention of §4) → all N, T; reason: the proof of this lemma uses no largeness; the statement specializes to large N, T
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Lemma 7, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_FewExperts_harvest

namespace FewExperts

/-- **Lemma 7 (failure needs a bad bet or a failed recursion).**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 7, p.18 (PDF 19): "If A fails, then it must have either transitioned with a
bad index, or A′ must have failed."

Under the hypotheses of Proposition 2, for every threshold tape `τ`: if the run
`A = HarvestGain(ℓ, T̃, B)` fails (it stops at a round `t` with `G_t^A < G_t^B + αℓ − 16√T̃`), then
`A` transitioned, at some `(t*, i*, r*)`, and either `r*` is a bad index of `i*`, or the recursive
run `A′ = HarvestGain(ℓ, T̃′, B′)` — horizon `T̃′ = min(⌊T̃/2⌋, T̃ − t*)`, baseline the two-expert
Hedge `B′` on `B` and `i*`, gains from round `t* + 1`, thresholds of depth `≥ 1` — fails (for its
own baseline `B′` and horizon `T̃′`).

**Formalization Note** "Fails" is (6) of Proposition 2 (ii) (`HGRun.Fails`). -/
theorem lemma_7_failure (N T : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (hαℓ : 1 ≤ alpha N T * ℓ) (Ttil : ℕ)
    (hT1 : 1 ≤ Ttil) (hTT : Ttil ≤ T) (b h : ℕ → Fin N → ℝ)
    (hb : ∀ u, 1 ≤ u → u ≤ Ttil → IsProbVec (b u)) (hh : IsGainSeq Ttil h) (τ : ThrTape N)
    (hfail : (harvest N T ℓ Ttil b h τ).Fails (alpha N T) ℓ Ttil b h) :
    ∃ ts is rs, transOf N T ℓ Ttil b h (τ 0) = some (ts, is, rs) ∧
      (IsBadIndex N T ℓ Ttil b h is rs ∨
        (harvest N T ℓ (phase2Horizon Ttil ts) (hedgePairPred b h ts is (phase2Horizon Ttil ts))
            (fun u => h (ts + u)) (fun d => τ (d + 1))).Fails (alpha N T) ℓ
          (phase2Horizon Ttil ts) (hedgePairPred b h ts is (phase2Horizon Ttil ts))
          (fun u => h (ts + u))) := by sorry

end FewExperts
