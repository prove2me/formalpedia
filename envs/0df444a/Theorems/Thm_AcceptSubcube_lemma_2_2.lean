-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_2_2
-- name    : AcceptSubcube.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:19.897356+00:00
-- url     : https://prove2.me/theorems/bf115ddf-a13e-40c0-8a4d-d06d327a5b1e
-- title:
--   Lemma 2.2 — equivalent formulations of the pinning property $\mathsf P_t$
-- statement:
--   Let $k\ge2$, let $P:\{0,1\}^k\to\{0,1\}$ be a nontrivial predicate and $0\le t\le k-1$. The following are equivalent:
--
--   1. $P$ has the pinning property $\mathsf P_t$;
--   2. for every set $S$ of $t$ coordinates, the restrictions to $S$ of the rejected patterns $P^{-1}(0)$ are all $2^t$ patterns on $S$;
--   3. $h(P)\le k-t-1$;
--   4. no assignment to at most $t$ coordinates forces acceptance: for $|S|\le t$ and every $a$, the subcube $Q(S,a)$ is not accepting.
--
--   In particular $h(P)\le h$ is the property $\mathsf P_{k-h-1}$, which is how the class $\mathcal C_{k,h}$ enters the pinning step of the algorithm.
--
--   Differences from the source:
--   - reading: a k-ary predicate (§2: "Fix an arity k ≥ 2") → 2 ≤ k; reason: standing assumption of §2, p.9
--   - encoding: P^{-1}(0) projects onto all 2^t patterns on every t coordinates → for every t-set S the image of the rejection set under restriction to S has 2^t elements; reason: there are exactly 2^t patterns on S, so the two say the same
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 2.2, p.10

import Mathlib
import Definitions.Def_AcceptSubcube_subcubeDim

namespace AcceptSubcube

/-- **Lemma 2.2 (Equivalent formulations).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 2.2, p.10: "For a nontrivial k-ary
predicate P and 0 ≤ t ≤ k − 1, the following are equivalent: (i) P has P_t; (ii) the rejection set
P^{−1}(0) projects onto all 2^t patterns on every t coordinates; (iii) h(P) ≤ k − t − 1; (iv) no
assignment to at most t coordinates forces acceptance."

(ii) is stated as: for every `t`-set `S` of coordinates, the image of `P^{−1}(0)` under restriction
to `S` has `2^t` elements. (iv): for no `S` with `|S| ≤ t` and no values on `S` is the subcube
accepting.

**Formalization Note.** `k ≥ 2` is §2's standing arity ("Fix an arity k ≥ 2", p.9). -/
theorem lemma_2_2 (k t : ℕ) (hk : 2 ≤ k) (ht : t ≤ k - 1) (P : (Fin k → Bool) → Bool)
    (hP : PredNontrivial P) :
    [HasPt t P,
      ∀ S : Finset (Fin k), S.card = t →
        ((Finset.univ.filter (fun y => P y = false)).image (fun y => fun i : S => y i)).card =
          2 ^ t,
      subcubeDim P ≤ k - t - 1,
      ∀ S : Finset (Fin k), S.card ≤ t → ∀ a : Fin k → Bool, ¬ AcceptsSubcube P S a].TFAE := by sorry

end AcceptSubcube
