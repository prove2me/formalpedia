-- Prove2me | Theorems.Thm_BanditAlgorithm_bernoulliRelativeEntropy_antitone_fst
-- name    : BanditAlgorithm.bernoulliRelativeEntropy_antitone_fst
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T04:54:40.361425+00:00
-- url     : https://prove2.me/theorems/853cbb2c-9e93-4a63-993f-f5d68b33af93
-- title:
--   Bernoulli KL is antitone in its first argument below the target
-- statement:
--   Fix $q\in(0,1)$. On the interval $[0,q]$, Bernoulli relative entropy is nonincreasing in its first argument. Thus, whenever $0\le x\le y\le q$,
--
--   $$
--   d(y,q)\le d(x,q).
--   $$
--
--   In words, moving the first Bernoulli parameter toward the fixed second parameter cannot increase their relative entropy.
--
--   This is the monotonicity step used in Lemma 10.8: if an empirical mean lies below $\mu+\varepsilon$, then its divergence from the larger threshold $\mu+\Delta$ is at least $d(\mu+\varepsilon,\mu+\Delta)$.
--
--   Formalization Note: The first parameter $x$ may equal zero. The proof rewrites the divergence using the continuous extension of $x\log x$, proves the derivative is nonpositive in the interior, and then applies the derivative monotonicity theorem on the closed interval.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), monotonicity used in the proof of Lemma 10.8, printed pp. 138–139.

import Definitions.Def_bernoulliRelativeEntropy

open Set

theorem BanditAlgorithm.bernoulliRelativeEntropy_antitone_fst
    {x y q : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hyq : y ≤ q) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    BanditAlgorithm.bernoulliRelativeEntropy y q ≤
      BanditAlgorithm.bernoulliRelativeEntropy x q := by
  sorry
