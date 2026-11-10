-- Prove2me | Theorems.Thm_DQILocal_Recon_lemma_5_3
-- name    : DQILocal.Recon.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:01.643826+00:00
-- url     : https://prove2.me/theorems/78942c89-97a8-4082-b9f5-870e848f9316
-- title:
--   Lemma 5.3 — $\mathrm{TP}_t(i)$ from a kernel condition: every $z\in\ker M$ extends to some $\kappa\in\ker B$
-- statement:
--   Let $q\ge2$, $B$ any 0/1 matrix over $\mathbb Z_q$, $i$ a symbol and $t\ge0$. Write $E$ for the set of checks not in $F_t(i)$, and let $M$ be the submatrix of $B$ with rows $[m]\setminus N_t(i)$ and columns $E$. If every $z\in\ker M$ is the restriction to $E$ of some $\kappa\in\ker B$, then $\mathrm{TP}_t(i)$ holds.
--
--   This reduces the tree projection condition to a statement about the kernel of a submatrix, which the first-moment method then controls in random instances.
--
--   Differences from the source:
--   - encoding: z ∈ ℤ_q^E with M z = 0 → z : κ → ℤ_q vanishing on F_t(i) with Σ_a B_{ja} z_a = 0 for every symbol j ∉ N_t(i); reason: vectors on E are vectors on all checks vanishing on F_t(i); same condition
--   - encoding: checks indexed by [n] → checks indexed by any finite type κ; reason: a relabelling of the checks; same instances
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.3, p. 31 (context: p. 31)

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions

namespace DQILocal.Recon

open scoped BigOperators

/-- **Lemma 5.3 (tree projection from a kernel condition).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.3, p. 31.
Context (p. 31): "Write `E` for the set of checks not in `F_t(i)`, and let `M` be the submatrix of
`B` with rows `[m] \ N_t(i)` and columns `E`." Statement: "If every `z ∈ ker M` is the restriction
to `E` of some `κ ∈ ker B`, then `TP_t(i)` holds."

**Formalization Note.** A vector `z ∈ ℤ_q^E` is encoded as `z : κ → ℤ_q` vanishing on `F_t(i)`;
`z ∈ ker M` says `Σ_a B_{ja} z_a = 0` for every symbol `j ∉ N_t(i)`. Kernels are over `ℤ_q`. Any
0/1 matrix `B`, any `q ≥ 2`. -/
theorem lemma_5_3 (q : ℕ) [NeZero q] (hq : 2 ≤ q) {m : ℕ} {κ : Type} [Fintype κ]
    (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ)
    (h : ∀ z : κ → ZMod q, (∀ a, a ∈ ballChk B i t → z a = 0) →
      (∀ j, j ∉ ballSym B i t → ∑ a, toZMod q B j a * z a = 0) →
        ∃ v : κ → ZMod q, (toZMod q B).mulVec v = 0 ∧ ∀ a, a ∉ ballChk B i t → v a = z a) :
    TP q B i t := by sorry

end DQILocal.Recon
