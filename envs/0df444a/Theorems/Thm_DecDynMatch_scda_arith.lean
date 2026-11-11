-- Prove2me | Theorems.Thm_DecDynMatch_scda_arith
-- name    : DecDynMatch.scda_arith
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:21.285206+00:00
-- url     : https://prove2.me/theorems/c2d19454-1957-4535-ad97-b0a3cf2a437e
-- title:
--   §3.2, p.10 — the case $g(t)=t$: $F_g(x)=H+2x$ and logarithmic iteration counts
-- statement:
--   Let $K\ge 2$ and take $g(t)=t$. Then
--
--   1. $s_{j+1}=2s_j$ for every $j$;
--   2. $F_g(x)=H+2x$ for every $x\ge 1$, so $\Pi_g$ is SC-DA;
--   3. $N_g(T)\le\lfloor\log_2 T\rfloor+1$ for every $T$, i.e. $N_g(T)=O(\log T)$;
--   4. the SC-DA rule $F(x)=H+2x$ satisfies (12);
--   5. for this rule $\Psi_F^{\circ3}(x)=27x+78H$;
--   6. for this rule $N_F(T)\le\lfloor\log_2 T\rfloor+1$;
--   7. $H\le 16K^2$ and $U\le 9K^2$.
--
--   Together with (30), items 5–7 give Theorem 1: $D(T;I)\le 27(t^*+1)+78H+U(\log_2T+1)=O(t^*+K^2\log T)$ with constants uniform in $K$.
--
--   Differences from the source:
--   - reading: N_g(T) = O(log T) → N_g(T) ≤ ⌊log₂ T⌋ + 1 for every T; reason: the explicit bound implies the O(·) statement; the stronger reading
--   - generalization: the p.10 sentence (s_{j+1} = 2s_j, F_g(x) = H + 2x, N_g(T) = O(log T)) → also (12) for H + 2x, Ψ³(x) = 27x + 78H, N_F(T) ≤ ⌊log₂ T⌋ + 1, H ≤ 16K², U ≤ 9K²; reason: these are the facts of p.21 by which (30) yields Theorem 1; added conjuncts imply the sentence
--   - encoding: max({g(s_j) − s_j : 64 s_j ≤ x} ∪ {0}) and #{j ≥ 0 : s_j < T} → Finset.sup of truncated differences over j ≤ x, and a count over j < T; reason: truncating negative differences does not change a maximum containing 0; for g ≥ 1 no index is lost
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §3.2, p.10; App. A.5, p.21

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_Psi
import Definitions.Def_DecDynMatch_NF
import Definitions.Def_DecDynMatch_Fg

namespace DecDynMatch

/-- **The specialization g(t) = t.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), §3.2, p.10: "Finally, taking g(t) = t gives the SC-DA protocol. In this case,
s_{j+1} = 2s_j, F_g(x) = H + 2x, and we have N_g(T) = O(log T), establishing Theorem 1." With the
facts of App. A.5, p.21, used to turn (30) into Theorem 1: "z₃ = 27(t + 1) + 78H" (the threefold
recovery map for F(x) = H + 2x) and "Here H ≤ 16K² and U ≤ 9K²".

For `K ≥ 2` and `g = id`:
1. `s_{j+1} = 2 s_j`;
2. `F_g(x) = H + 2x` for `x ≥ 1`;
3. `N_g(T) ≤ ⌊log₂ T⌋ + 1` for every `T` (the explicit form of `N_g(T) = O(log T)`);
4. `F(x) = H + 2x` satisfies (12);
5. `Ψ_F^{∘3}(x) = 27x + 78H` for `F(x) = H + 2x`;
6. `N_F(T) ≤ ⌊log₂ T⌋ + 1` for `F(x) = H + 2x`;
7. `H ≤ 16K²` and `U ≤ 9K²`. -/
theorem scda_arith (K : ℕ) (hK : 2 ≤ K) :
    (∀ j, sseq K id (j + 1) = 2 * sseq K id j) ∧
    (∀ x, 1 ≤ x → Fg K id x = H K + 2 * x) ∧
    (∀ T, Ng K id T ≤ Nat.log 2 T + 1) ∧
    RuleOK K (scdaRule K) ∧
    (∀ x, (Psi K (scdaRule K))^[3] x = 27 * x + 78 * H K) ∧
    (∀ T, NF K (scdaRule K) T ≤ Nat.log 2 T + 1) ∧
    H K ≤ 16 * K ^ 2 ∧ U K ≤ 9 * K ^ 2 := by sorry

end DecDynMatch
