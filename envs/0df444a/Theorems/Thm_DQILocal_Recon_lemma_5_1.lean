-- Prove2me | Theorems.Thm_DQILocal_Recon_lemma_5_1
-- name    : DQILocal.Recon.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:05:59.506678+00:00
-- url     : https://prove2.me/theorems/87f23a10-70d9-429e-99cd-154650f06420
-- title:
--   Lemma 5.1 — $\mathrm{TP}_t(i)$ iff every vector of $K$ supported in $N_t(i)$ is a combination of the columns indexed by $F_t(i)$
-- statement:
--   Let $q\ge2$, $B$ any 0/1 matrix over $\mathbb Z_q$, $i$ a symbol and $t\ge0$.
--
--   1. $\mathrm{TP}_t(i)$ holds if and only if every vector $w\in K$ supported in $N_t(i)$ is a $\mathbb Z_q$-linear combination of the columns of $B$ indexed by $F_t(i)$, i.e. $w=Bx$ for some $x$ vanishing off $F_t(i)$.
--   2. In particular, $\mathrm{TP}_t(i)$ holds if no nonzero combination of the columns indexed by checks outside $F_t(i)$ is supported in $L_t(i)$: if every $x$ vanishing on $F_t(i)$ with $Bx$ supported in $L_t(i)$ has $Bx=0$, then $\mathrm{TP}_t(i)$ holds.
--
--   This characterizes the tree projection condition through the vectors of $K=C^\perp$, which is the starting point of the first-moment argument of §5.1.
--
--   Differences from the source:
--   - encoding: columns indexed by checks [n] → checks indexed by any finite type κ; reason: every finite index set is a relabelling of [n]; same instances
--   - encoding: "no nonzero combination … is supported in L_t(i)" → every combination B x (x vanishing on F_t(i)) supported in L_t(i) equals 0; reason: the same condition, stated positively
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.1, p. 30

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions

namespace DQILocal.Recon

open scoped BigOperators

/-- **Lemma 5.1 (tree projection through `K`).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 5.1, p. 30.
"The condition `TP_t(i)` holds if and only if every vector of `K` supported in `N_t(i)` is a
`ℤ_q`-linear combination of the columns of `B` indexed by `F_t(i)`. In particular, `TP_t(i)` holds
if no nonzero combination of the columns indexed by checks outside `F_t(i)` is supported in
`L_t(i)`."

**Formalization Note.** Any 0/1 matrix `B` (no regularity), any symbol `i`, any `t`, any `q ≥ 2`
(`ℤ_q` need not be a field). A combination of the columns indexed by a set `F` is `B x` with `x`
vanishing off `F`; "nonzero combination" means that the vector `B x` is nonzero. -/
theorem lemma_5_1 (q : ℕ) [NeZero q] (hq : 2 ≤ q) {m : ℕ} {κ : Type} [Fintype κ]
    (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) :
    (TP q B i t ↔ ∀ w ∈ imageK q B, (∀ j, j ∉ ballSym B i t → w j = 0) →
      ∃ x : κ → ZMod q, (∀ a, a ∉ ballChk B i t → x a = 0) ∧ w = (toZMod q B).mulVec x) ∧
    ((∀ x : κ → ZMod q, (∀ a, a ∈ ballChk B i t → x a = 0) →
        (∀ j, j ∉ leaves B i t → (toZMod q B).mulVec x j = 0) → (toZMod q B).mulVec x = 0) →
      TP q B i t) := by sorry

end DQILocal.Recon
