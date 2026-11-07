-- Prove2me | Theorems.Thm_BoolCSPDel_integer_gap
-- name    : BoolCSPDel.integer_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:15.450214+00:00
-- url     : https://prove2.me/theorems/2ca09277-7f48-4a53-95ce-13bcaed22a23
-- title:
--   Proof of Theorem 5.1 — $G\preceq W+I/(4D)$ forces $\mathrm{Sat}(S)=\mathrm{Sat}(f)$
-- statement:
--   Let $B$ have the representation property of Lemma 5.2, $f\ge0$, $S$ a set of active constraints, $w>0$ on $S$, and $W=\sum_{C\in S}w_Cb_Cb_C^\top$. If
--
--   $$B^\top\mathrm{diag}(f)^2B\preceq W+\frac1{4D}I,$$
--
--   then $\mathrm{Sat}_\Gamma(S)=\mathrm{Sat}_\Gamma(f)$.
--
--   This is the step that turns a spectral approximation into an exact sparsifier.
--
--   Differences from the source:
--   - generalization: one relation R of arity k → a finite language Γ of relations of arity at most k; reason: the paper states this form on the cited page and uses it; Γ = {R} is the printed case
--   - generalization: B, ϕ of Lemma 5.2 → any integer matrix on the monomial coordinates with the representation property; reason: the B of Lemma 5.2 has this property; only it is used
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), proof of Theorem 5.1, p.32; proof of Corollary 5.10, p.37

import Mathlib
import Definitions.Def_BoolCSPDel_Mono

namespace BoolCSPDel

/-- **The integer gap step.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), proof of Theorem 5.1, p.32, and proof of Corollary 5.10, p.37: from
`G ⪯ W + I/(4D)` with `W = Σ_{C ∈ S} w_C b_C b_Cᵀ`, `S` active and `w > 0`, "The integer gap in Lemma 5.2
forces this energy to be zero … Hence `Sat_R(S) = Sat_R(f)`."

**Formalization Note.** `B` is any integer matrix with the representation property of Lemma 5.2. -/
theorem integer_gap {k : ℕ} {Γ : Lang k} {n d : ℕ} (B : Matrix (Con Γ (Fin n)) (Mono n d) ℤ)
    (hB : IsPolyRep B) (f : Con Γ (Fin n) → ℤ) (hf : ∀ C, 0 ≤ f C) (S : Finset (Con Γ (Fin n)))
    (hS : ∀ C ∈ S, 0 < f C) (w : Con Γ (Fin n) → ℝ) (hw : ∀ C ∈ S, 0 < w C)
    (hG : LoewnerLE (gramR B f)
      (weightedSum B S w + (1 / (4 * (Fintype.card (Mono n d) : ℝ))) • (1 : Matrix _ _ ℝ))) :
    SatSet S = Sat f := by sorry

end BoolCSPDel
