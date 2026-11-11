-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_entropy_subadditivity
-- name    : EliasGlobalClock.LowerBound.entropy_subadditivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:59.978712+00:00
-- url     : https://prove2.me/theorems/465e01d5-db01-438d-a035-41cd22960820
-- title:
--   Fact D.2 — subadditivity for arbitrary heterogeneous finite laws
-- statement:
--   Let $S_1,\ldots,S_\ell$ be finite sets and let $\mu$ be any joint probability law on $S_1\times\cdots\times S_\ell$. Write $\mu_j$ for its coordinate marginals. With entropy $H$ in nats and the convention $0\ln0=0$,
--
--   $$H(\mu)\le\sum_{j=1}^{\ell}H(\mu_j).$$
--
--   No coordinate independence, common coordinate alphabet, rationality or uniform sampling assumption is required. This is the entropy comparison needed for the two half-population activity vectors, whose time coordinates can be dependent.
--
--   Differences from the source:
--   - encoding: a joint law on S₁×⋯×Sℓ and its marginals → a PMF on a dependent product indexed by Fin ℓ, with marginals given by PMF.map; reason: finite alphabets are relabelled from 1,…,ℓ to 0,…,ℓ−1; arbitrary real-valued masses are retained, including zeros
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.36, PDF p.37, Fact D.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_finiteEntropy

open scoped BigOperators

namespace EliasGlobalClock.LowerBound

/-- Fact D.2, printed p.36 / PDF p.37: arbitrary heterogeneous finite laws. -/
theorem entropy_subadditivity (ℓ : ℕ) (S : Fin ℓ → Type*) [∀ j, Fintype (S j)]
    (μ : PMF (∀ j, S j)) :
    finiteEntropy μ ≤ ∑ j : Fin ℓ, finiteEntropy (μ.map (fun z => z j)) := by sorry

end EliasGlobalClock.LowerBound
