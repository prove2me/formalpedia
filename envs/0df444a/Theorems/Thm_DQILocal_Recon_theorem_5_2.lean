-- Prove2me | Theorems.Thm_DQILocal_Recon_theorem_5_2
-- name    : DQILocal.Recon.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:34.733643+00:00
-- url     : https://prove2.me/theorems/a873b49d-dec5-48c9-a62f-f4207d328422
-- title:
--   Theorem 5.2 — locality bound: under $\mathrm{LT}_t(i)$ and $\mathrm{TP}_t(i)$ every $t$-local estimate errs with probability at least $1-P_t\ge1-P_\infty$
-- statement:
--   Let $q\ge2$, $f$ a cost, $\beta\ge0$, $k,D\ge2$, let $B$ be $(k,D)$-regular, and suppose that $\mathrm{LT}_t(i)$ and $\mathrm{TP}_t(i)$ hold. Then:
--
--   1. every decoder for the decoding problem with the product amplitude function that makes a $t$-local estimate at $i$ has symbol error at $i$ at least
--   $$1-P_t\;\ge\;1-P_\infty,\qquad P_\infty=\lim_{t\to\infty}P_t ,$$
--   and its block success is at most $P_t$;
--   2. if the primal model has reconstruction, then $1-P_\infty>0$;
--   3. for $q=2$ and $f(z)=z$, the bound is at least $\frac14\sigma_\beta^2\,\bar{\mathfrak m}_\infty^{2k}$, i.e. $1-P_t\ge\frac14\sigma_\beta^2\bar{\mathfrak m}_\infty^{2k}$.
--
--   So a decoder whose estimate of a symbol depends only on the qudits within distance $2t$ cannot beat the optimal tree decoder.
--
--   Differences from the source:
--   - encoding: a measurement (possibly with ancillas and work registers) → a POVM on the system (positive semidefinite elements summing to the identity); reason: Naimark dilation: the two describe the same outcome laws
--   - encoding: P_∞ = lim_{t→∞} P_t and m̄_∞ = lim m̄_t → ⨆ t, P_t and ⨅ t, m̄_t; reason: monotone bounded sequences; same values
--   - encoding: "for q = 2 and f(z) = z" → hypotheses q = 2 and ∀ z, f z = z.val inside the statement for general q; reason: the clause applies exactly in that case
--   - encoding: checks indexed by [n] → checks indexed by any finite type κ; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 5.2, p. 30

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Reconstruction

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder

/-- **Theorem 5.2 (Locality bound).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 5.2, p. 30.
"Let `B` be `(k, D)`-regular, and suppose that `LT_t(i)` and `TP_t(i)` hold. Then every decoder for
the decoding problem with the product amplitude function that makes a `t`-local estimate at `i` has
symbol error at `i` at least `1 - P_t ≥ 1 - P_∞`, `P_∞ = lim_{t→∞} P_t`. If the primal model has
reconstruction, then `1 - P_∞ > 0`. For `q = 2` and `f(z) = z`, the bound is at least
`(1/4) σ_β² m̄_∞^{2k}`. In every case the block success of the decoder is at most `P_t`."

**Formalization Note.** A decoder is a POVM `F` on the `m` qudits with outcomes in `ℤ_q^m`
(Definition 3.2; ancillas absorbed by Naimark), the received state is
`⊗_j |ψ^{p_β}_{c_j}⟩` (product amplitude function of Gibbs form). The binary clause is stated for
`q = 2` and `f(z) = z.val`, with `σ_β = tanh(β/2)` and `m̄_∞ = inf_t m̄_t`. Standing assumptions
`q ≥ 2`, `β ≥ 0`, `k ≥ 2`, `D ≥ 2` (§3.1, p. 15). The check index set is any finite type. -/
theorem theorem_5_2 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (k D : ℕ) (hk : 2 ≤ k) (hD : 2 ≤ D) {m : ℕ} {κ : Type} [Fintype κ]
    (B : Matrix (Fin m) κ Bool) (hB : IsRegular k D B) (i : Fin m) (t : ℕ) (hLT : LT B i t)
    (hTP : TP q B i t) :
    (∀ F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ, IsPOVM F →
      IsLocalEstimate q (gibbsWeight q f β) B i t F →
        1 - Pt k D q f β t ≤ symbolError (gibbsWeight q f β) B F i ∧
          blockSuccess (gibbsWeight q f β) B F ≤ Pt k D q f β t) ∧
    1 - Pinf k D q f β ≤ 1 - Pt k D q f β t ∧
    (HasRecon k D q f β → 0 < 1 - Pinf k D q f β) ∧
    (q = 2 → (∀ z : ZMod q, f z = (z.val : ℝ)) →
      (1 / 4) * Real.tanh (β / 2) ^ 2 * mbarInf k D q f β ^ (2 * k) ≤ 1 - Pt k D q f β t) := by sorry

end DQILocal.Recon
