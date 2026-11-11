-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim14_shifted_walk_uniform
-- name    : ExpanderWalkDecode.Main.claim14_shifted_walk_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:41.275415+00:00
-- url     : https://prove2.me/theorems/95aa5f80-6c41-44c0-9827-53f3605f151a
-- title:
--   Claim 14 (Claim 5 of [RR23b]) — first blocks of short shifted walks are uniform
-- statement:
--   Let $B$ be a Cayley graph on $(\mathbb F_2^m)^s$, $s\ge1$, with generators $u_1,\dots,u_q$, $q\ge1$. For every $k\le s$, the first blocks $(\hat b_1,\dots,\hat b_k)$ of the forward shifted walk ($b_1$ uniform, $b_{i+1}=\mathrm{shift}(b_i+u_j)$ with $j$ uniform) and of the reverse shifted walk ($b_k$ uniform, $b_{i-1}=\mathrm{shift}^{-1}(b_i)+u_j$ with $j$ uniform) are both uniformly distributed:
--   $$\big(\hat b_1,\dots,\hat b_k\big)\ \sim\ \mathrm{Unif}\big((\mathbb F_2^m)^k\big)\quad\text{under }\overrightarrow{\mathrm{RW}}{}^k_B\text{ and under }\overleftarrow{\mathrm{RW}}{}^k_B .$$
--
--   This pseudorandomness property is what makes short wide replacement walks look like ordinary random walks in $A$ (property (P3)).
--
--   **Formalization Note** Equality of distributions is stated as equality of the expectations of every real test function.
--
--   Differences from the source:
--   - generalization: B from Proposition 5 → any Cayley graph on (F_2^m)^s with q ≥ 1 generators; reason: the argument uses only the shift structure; specializes to the source's B
--   - encoding: equality of laws ≡ → equal expectations of every test function; the latent generator vector has length k (one unused coordinate); reason: same distributions
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 22 (PDF p. 25), Appendix B.2, Claim 14

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 14 (Claim 5 of [RR23b]) (Appendix B.2, p. 22): for `k ≤ s`, the first blocks
`(b̂₁, …, b̂_k)` of the forward shifted walk (`b₁` uniform, `b_{i+1} = shift(b_i + u_j)`) and of the
reverse shifted walk (`b_k` uniform, `b_{i-1} = shift⁻¹(b_i) + u_j`) are both uniformly distributed
on `(F₂^m)^k`. Equality of laws is stated as equality of expectations of every test function. -/
theorem claim14_shifted_walk_uniform {m s q : ℕ} (u : Fin q → Inner m s) (hs : 0 < s) (hq : 0 < q)
    (k : ℕ) (hk : k ≤ s) (F : (Fin k → Fin m → ZMod 2) → ℝ) :
    (avg fun bj : Inner m s × (Fin k → Fin q) => F fun i => hat (bseq u bj.1 bj.2 i)) = avg F ∧
    (avg fun bj : Inner m s × (Fin k → Fin q) => F fun i => hat (rbseq u bj.1 bj.2 (k - 1 - i)))
      = avg F := by sorry

end ExpanderWalkDecode.Main
