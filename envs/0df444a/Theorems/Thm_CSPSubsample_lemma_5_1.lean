-- Prove2me | Theorems.Thm_CSPSubsample_lemma_5_1
-- name    : CSPSubsample.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:15.727968+00:00
-- url     : https://prove2.me/theorems/269dcfef-2227-42a7-ab6b-0685619c46a5
-- title:
--   Lemma 5.1 (Decomposition) — $\mathrm{val}^{\mathrm{bal}}_U$ splits into a $U_{-t}$ part and the $H_{i,U_{-t}}$ terms
-- statement:
--   Let $U\subseteq[n]$, let $\phi\in[q]^U$ and fix a block $t\in[T]$. Then
--   $$
--   \mathrm{val}^{\mathrm{bal}}_U(\phi)=\frac1{|U|^k}\sum_{w\in M(U_{-t})}P_w(\phi|_w)+\frac1{|U|^k}\sum_{i\in U_t}H_{i,U_{-t}}(\phi_i,\phi).
--   $$
--   A balanced constraint meets block $t$ in at most one variable, so the best value of a variable of $U_t$ can be chosen locally, given the rest. The extender of §5.2 is built on this.
--
--   Differences from the source:
--   - generalization: blocks V_1, …, V_T of size approximately n/T → an arbitrary block map b : [n] → [T]; reason: the statement holds for every partition of [n] into T blocks; it specializes to the paper's blocks
--   - encoding: an assignment ϕ ∈ [q]^U → a total assignment ϕ ∈ [q]^n; reason: the balanced value on U reads ϕ only on U
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 5.1, p.13 (PDF p.15); restated with proof p.27 (PDF p.29)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valbal

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 5.1 (Decomposition)** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.13 = PDF p.15;
restated with proof p.27 = PDF p.29). For `U ⊆ [n]`, an assignment `ϕ ∈ [q]^U` and `t ∈ [T]`,
`val^bal_U(ϕ) = (1/|U|^k) ∑_{w ∈ M(U_{−t})} P_w(ϕ|_w) + (1/|U|^k) ∑_{i ∈ U_t} H_{i,U_{−t}}(ϕ_i, ϕ)`.

**Formalization Note** Stated for every block map `b : Fin n → Fin T`; `ϕ` is total (only its
values on `U` are read). -/
theorem lemma_5_1 {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T) (U : Finset (Fin n))
    (ϕ : Fin n → Fin q) (t : Fin T) :
    valbal I b U ϕ = 1 / (U.card : ℝ) ^ k * sumBal I b (blockCompl b U t) ϕ +
      1 / (U.card : ℝ) ^ k * ∑ i ∈ blockPart b U t, Hval I b i (blockCompl b U t) (ϕ i) ϕ := by sorry

end CSPSubsample
