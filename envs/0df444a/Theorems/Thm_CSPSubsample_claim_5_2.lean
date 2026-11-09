-- Prove2me | Theorems.Thm_CSPSubsample_claim_5_2
-- name    : CSPSubsample.claim_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:32.938379+00:00
-- url     : https://prove2.me/theorems/432add17-2d93-474f-acd2-7e5bfdf72b01
-- title:
--   Claim 5.2 — the seed $\tilde\sigma=(\phi^{(t-1)}|_{S_t})_t$ gives $D_{\mathcal S}(\tilde\sigma)|_U=\phi^{(T)}$
-- statement:
--   Let $U\subseteq[n]$ and $\mathcal S=(S_t)_{t\in[T]}$ with $S_t\subseteq U_{-t}$, and let $\phi^{(0)},\dots,\phi^{(T)}$ be the best-response sequence of eq. (7). The seed $\tilde\sigma=(\phi^{(t-1)}|_{S_t})_{t\in[T]}$ satisfies
--   $$
--   D_{\mathcal S}(\tilde\sigma)|_U=\phi^{(T)},
--   $$
--   that is, $D_{\mathcal S}(\tilde\sigma)_i=\phi^{(T)}_i$ for every $i\in U$. So $\Psi(\mathcal S)$ contains an assignment that agrees on $U$ with the end of the best-response sequence.
--
--   Differences from the source:
--   - generalization: blocks V_1, …, V_T of size approximately n/T → an arbitrary block map b : [n] → [T]; reason: the statement holds for every partition of [n] into T blocks; it specializes to the paper's blocks
--   - generalization: ϕ^{(0)} = ϕ*, an optimal balanced assignment on U → any starting assignment ϕ^{(0)}; reason: the claim does not use optimality; it specializes at ϕ^{(0)} = ϕ*
--   - generalization: ties in arg max broken in an arbitrary but deterministic way, consistently in (6) and (7) → an arbitrary maximizer-choosing rule tb (which may depend on the variable i), the same rule in (6) and (7); reason: the paper's rule is one such rule
--   - encoding: a seed σ̄ ∈ ⨉_{t∈[T]} [q]^{S_t} → σ : [T] → [n] → [q], of which only σ_t on S_t is read; reason: the extender reads σ_t only on S_t, so the two seed spaces give the same assignments
--   - encoding: ϕ^{(0)}, …, ϕ^{(T)} ∈ [q]^U → total assignments in [q]^n, the variables outside U keeping their value under ϕ^{(0)}; reason: the statement reads these assignments only on U (agreement on U, val^bal_U, H_{i,V} with V ⊆ U), and the recursion (7) reads ϕ^{(t−1)} only on S_t ⊆ U
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Claim 5.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valbal
import Definitions.Def_CSPSubsample_extender

set_option autoImplicit false

namespace CSPSubsample

/-- **Claim 5.2** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.14 = PDF p.16). In the setting of
§5.3 (an arbitrary `U` and a tuple `S` with `S_t ⊆ U_{−t}`), the seed
`σ̃ = (ϕ^{(t−1)}|_{S_t})_{t ∈ [T]}` guarantees `D_S(σ̃)|_U = ϕ^{(T)}`.

**Formalization Note** `ϕ^{(t)}` is `phiSeq … ϕ0 t` (eq. (7)), `σ̃` is `seedOf`, `D_S` is
`extender`; `|_U` is agreement at every `i ∈ U`. The statement holds for every starting
assignment `ϕ0` (the paper starts at a maximizer `ϕ*`), every block map and every tie-breaking
rule `tb` used consistently in (6) and (7). -/
theorem claim_5_2 {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T) (U : Finset (Fin n))
    (S : Fin T → Finset (Fin n)) (hS : ∀ t, S t ⊆ blockCompl b U t)
    (tb : Fin n → (Fin q → ℝ) → Fin q) (htb : IsArgmaxRule tb) (ϕ0 : Fin n → Fin q) :
    ∀ i ∈ U, extender I b S tb (seedOf I b U S tb ϕ0) i = phiSeq I b U S tb ϕ0 T i := by sorry

end CSPSubsample
