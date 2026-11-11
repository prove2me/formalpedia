-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_5_3
-- name    : AcceptSubcube.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:15.091747+00:00
-- url     : https://prove2.me/theorems/77ebc230-2e76-435e-a4d4-0f882544f9c8
-- title:
--   Lemma 5.3 — recovery near an original optimum: $r_b^\ell\le c_kB/\Pi_t$
-- statement:
--   Let $k\ge2$. There are constants $c_k>0$, $C_k$, $C'_k$ depending only on $k$ such that the following holds for every $0\le t\le k-2$ (with $\ell=k-t$), every orientation rule with the guarantee of Lemma 3.2, and every complete Boolean $k$-CSP $\mathcal I$ on $n\ge k$ variables with nontrivial predicates, property $\mathsf P_t$ and $B=\mathrm{OPT}>\Pi_t$. One recovery round runs Lemma 3.3 on every $\mathcal I_{S,a}$ for all dyadic budgets $b=1,2,4,\dots$ up to the first power of two at least $\binom{n-t}\ell$, with radius $r_b=\min\{n,\lceil C_\ell b^{1/\ell}\rceil\}$, and appends $a$ to every candidate. Then:
--
--   1. for every fixed optimum $\sigma^\star$, with probability at least $3/4$ some candidate $\tau$ produced with some budget $b$ satisfies $\mathrm{dist}(\tau,\sigma^\star)\le r_b$ and
--   $$r_b^\ell\le c_k\,B/\Pi_t ;$$
--   2. the round has at most $C_k\,2^t\Pi_t\log n$ branches;
--   3. every branch produces a list of at most $(n+2)^{C'_k}$ candidates.
--
--   The probability is over independent uniform draws in all branches.
--
--   Differences from the source:
--   - generalization: Lemma 3.3 run with the canonical orientation → every orientation rule with the guarantee of Lemma 3.2 (GoodOrient); reason: the canonical rule is one of them
--   - reading: with probability at least 3/4 → exact fraction of joint draws, independent and uniform over the branches; reason: the paper's ideal model with exact uniform sampling (p.28)
--   - reading: 2^tΠ_tO_k(log n) branches, each with a polynomial-size list → ≤ C_k 2^t Π_t log n branches and ≤ (n+2)^{C'_k} candidates per branch, constants depending on k only; reason: standard meaning of O_k and of polynomial size
--   - reading: complete Boolean k-CSP with P_t (§2, §5 standing: k ≥ 2, nontrivial predicates, n ≥ k, 0 ≤ t ≤ k − 2) → explicit hypotheses; reason: standing assumptions stated at p.9 and p.25
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.3, p.26

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_subcubeDim
import Definitions.Def_AcceptSubcube_star
import Definitions.Def_AcceptSubcube_GoodOrient
import Definitions.Def_AcceptSubcube_recoverSet
import Definitions.Def_AcceptSubcube_roundDraws

namespace AcceptSubcube

/-- **Lemma 5.3 (Recovery near an original optimum)**, for the paper's round.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.3, p.26: "Suppose B > Π_t. One
recovery round runs Lemma 3.3 on every I_{S,a} for all dyadic budgets b = 1, 2, 4, . . . up to the
first power of two at least (n−t choose ℓ), with radius r_b = min{n, ⌈C_ℓ b^{1/ℓ}⌉}, and appends a
to every candidate. For every fixed optimum σ⋆, with probability at least 3/4, some candidate τ
produced with some budget b satisfies dist(τ, σ⋆) ≤ r_b and r_b^ℓ ≤ c_k B/Π_t, (24) where c_k
depends only on k. The round has 2^t Π_t O_k(log n) branches, each with a polynomial-size list."

The round: for every branch `(S, a, b)` (`branches`), the recovery procedure of Lemma 3.3
(`recoverSet`) on the star `I_{S,a}` (`star`) with an independent uniform draw (`roundDraws`), and
`a` appended to every candidate (`extendStar`). For every `k ≥ 2` there are constants `c_k > 0` and
`C_k`, `C'_k` such that, for every `0 ≤ t ≤ k − 2`, every orientation rule with the guarantee of
Lemma 3.2, every complete Boolean `k`-CSP with `P_t` and `B = OPT > Π_t`, and every optimum `σ⋆`:
(1) the fraction of joint draws for which some branch `(S, a, b)` produces a candidate `τ` with
`dist(τ, σ⋆) ≤ r_b` and `r_b^ℓ ≤ c_k B/Π_t` is at least `3/4`; (2) the number of branches is at
most `C_k 2^t Π_t log n`; (3) every list has at most `(n + 2)^{C'_k}` members.

**Formalization Note.** Standing assumptions of §2 and §5 (pp.9, 25): `k ≥ 2`, `0 ≤ t ≤ k − 2`,
`ℓ = k − t`, a complete instance with nontrivial predicates, `n ≥ k`. The probability is the exact
fraction of the joint draws, uniform and independent over the branches (the paper's "ideal model
with exact uniform sampling", p.28). The orientation rule is any rule with the guarantee of Lemma
3.2 (`GoodOrient`), the canonical one being one of them. `c_k`, `C_k`, `C'_k` are chosen after `k`
and before everything else. -/
theorem lemma_5_3 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (c Cb : ℝ) (Cl' : ℕ), 0 < c ∧
      ∀ t : ℕ, t ≤ k - 2 →
      ∀ orient : List ℕ × List (List Bool) → List (List Bool × ℕ), GoodOrient orient →
      ∀ I : GInst, I.IsComplete k → I.Nontrivial → k ≤ I.n → InstPt t I →
        (I.n.choose t : ℝ) < (OPT I : ℝ) →
        (∀ σ : Fin I.n → Bool, cost I σ = OPT I →
          (3 : ℝ) / 4 ≤
            (((roundDraws I.n t (k - t)).filter (fun D =>
                ∃ br : Finset ℕ × Finset ℕ × ℕ, ∃ hbr : br ∈ branches I.n t (k - t),
                  ∃ τ' ∈ recoverSet orient (k - t) (star I br.1 br.2.1) (D br hbr),
                    hdist (extendStar I.n br.1 br.2.1 τ') σ ≤ rb (k - t) I.n br.2.2 ∧
                    ((rb (k - t) I.n br.2.2 : ℕ) : ℝ) ^ (k - t) ≤
                      c * (OPT I : ℝ) / (I.n.choose t : ℝ))).card : ℝ) /
              ((roundDraws I.n t (k - t)).card : ℝ)) ∧
        ((branches I.n t (k - t)).card : ℝ) ≤
          Cb * 2 ^ t * (I.n.choose t : ℝ) * Real.log (I.n : ℝ) ∧
        (∀ br ∈ branches I.n t (k - t), ∀ S' ∈ draws (k - t) (I.n - t) br.2.2,
          (recoverSet orient (k - t) (star I br.1 br.2.1) S').card ≤ (I.n + 2) ^ Cl') := by sorry

end AcceptSubcube
