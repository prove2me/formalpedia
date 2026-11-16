-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_6_1
-- name    : DQILocal.Recon.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:28:49.00529+00:00
-- url     : https://prove2.me/theorems/604a3168-136a-436d-ae09-1d2262ec1f10
-- title:
--   Theorem 6.1, p. 37 — local decoders succeed only without reconstruction
-- statement:
--   Fix $(k,D,q,f)$ with $q\ge2$, $k,D\ge2$, and $\beta\ge0$. Let $(B_n)$ be a sequence of $(k,D)$-regular matrices, and for each $n$ let $F^{(n)}$ be a decoder for the decoding problem of $B_n$ with the product amplitude function $\Phi_\beta$. Suppose that for each $n$ there are a radius $t_n$ and a symbol $i_n$ such that $\mathrm{LT}_{t_n}(i_n)$ and $\mathrm{TP}_{t_n}(i_n)$ hold and $F^{(n)}$ makes a $t_n$-local estimate at $i_n$. If the block success of the decoders tends to one,
--   $$\lim_{n\to\infty}\ \Pr_{c,\,F^{(n)}}\bigl[\hat c=c\bigr]=1,$$
--   then the primal model at $\beta$ has non-reconstruction.
--
--   So a local decoder can have block success close to one only at inverse temperatures without reconstruction. No condition on the growth of $t_n$ is required.
--
--   **Formalization Note** The number of rows and the check set may vary with $n$.
--
--   Differences from the source:
--   - encoding: a decoder (a measurement, possibly with ancillas) → a POVM on the received qudits with outcomes in Z_q^m; reason: Naimark dilation: the two describe the same outcome laws
--   - encoding: a sequence (B_n) with block success tending to one → m_n and the check type may vary with n; Tendsto (blockSuccess …) atTop (𝓝 1); reason: the source fixes neither; same statement
--   - encoding: checks indexed by [n] → checks indexed by any finite type; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.1, p. 37

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Reconstruction

namespace DQILocal.Recon.Supplement

open scoped BigOperators ComplexOrder
open DQILocal.Recon Filter Topology

/-- **Theorem 6.1 (Local decoders succeed only without reconstruction).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.1, p. 37.
"Fix `(k, D, q, f)` and `β ≥ 0`. Let `(B_n)` be a sequence of `(k, D)`-regular matrices, and for each
`n` let a decoder for the decoding problem of `B_n` with the product amplitude function `Φ_β` be
given. Suppose that for each `n` there are a radius `t_n` and a symbol `i_n` such that
`LT_{t_n}(i_n)` and `TP_{t_n}(i_n)` hold and the decoder makes a `t_n`-local estimate at `i_n`. If the
block success of the decoders tends to one, then the primal model at `β` has non-reconstruction."

**Formalization Note.** A decoder is a POVM on the `m_n` received qudits with outcomes in
`ℤ_q^{m_n}` (base Definition 3.2, ancillas absorbed). The number of rows `m_n` and the check type
`κ_n` may vary with `n`; no growth condition on `t_n` is imposed ("No condition on the growth of
`t_n` is needed", p. 37). Standing assumptions `q ≥ 2`, `k ≥ 2`, `D ≥ 2` (§3.1, p. 15). -/
theorem theorem_6_1 (k D q : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : 2 ≤ k) (hD : 2 ≤ D)
    (f : ZMod q → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (m : ℕ → ℕ) (κ : ℕ → Type) [∀ n, Fintype (κ n)] (B : ∀ n, Matrix (Fin (m n)) (κ n) Bool)
    (hB : ∀ n, IsRegular k D (B n))
    (F : ∀ n, (Fin (m n) → ZMod q) → Matrix (Fin (m n) → ZMod q) (Fin (m n) → ZMod q) ℂ)
    (hF : ∀ n, IsPOVM (F n)) (t : ℕ → ℕ) (i : ∀ n, Fin (m n))
    (hLT : ∀ n, LT (B n) (i n) (t n)) (hTP : ∀ n, TP q (B n) (i n) (t n))
    (hloc : ∀ n, IsLocalEstimate q (gibbsWeight q f β) (B n) (i n) (t n) (F n))
    (hsucc : Tendsto (fun n => blockSuccess (gibbsWeight q f β) (B n) (F n)) atTop (𝓝 1)) :
    NonRecon k D q f β := by sorry

end DQILocal.Recon.Supplement
