-- Prove2me | Theorems.Thm_ApproxGKR_lemma_C_3
-- name    : ApproxGKR.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:54.761138+00:00
-- url     : https://prove2.me/theorems/fcb08809-d558-4b19-a419-e7f447435244
-- title:
--   Lemma C.3 — approximate sum-check
-- statement:
--   Let $f$ have individual degree at most $D$ in $n_v\ge1$ variables, let $h,N\ge1$, $\Delta_0\ge0$, $0<\alpha<1$, $t_{n_v}\ge0$, and define backward
--   $$t_{j-1}=7\Delta_0+\frac{h(t_j+\Delta_0)}{\alpha},\qquad j=n_v,\dots,1.\tag{C.13}$$
--   Suppose the initial claim $Y_0$ differs from $\sum_{z\in H^{n_v}}f(z)$ by more than $t_0$. Then for every adaptive prover and every verifier implementation with arithmetic error at most $\Delta_0$, sum-check (degree check and residual tolerance $6\Delta_0$) rejects or ends with error $|Y_{n_v}-f(r)|>t_{n_v}$, except with probability at most
--   $$n_vD\big(\alpha^{1/D}+N^{-1}\big)$$
--   over the uniform challenges $r\in\Omega_N^{n_v}$.
--
--   This is the per-layer step of the soundness analysis.
--
--   Differences from the source:
--   - generalization: N a power of two, h = |H| a power of two → any N ≥ 1, h ≥ 1; reason: the proof does not use powers of two
--   - generalization: verifier computations as functions of the transcript so far → arbitrary functions of the challenge tuple within ∆₀; reason: covers every implementation; the bound holds for all of them
--   - encoding: probability over r ← Ω_N^{n_v} → the number of index tuples in (Fin N)^{n_v} at most N^{n_v} times the bound; reason: uniform measure as a count
--   - generalization: degree D (D ≥ 1 in Lemma C.2) → any D ≥ 0; reason: at D = 0 the bound is 0 and the statement still holds (the deterministic case)
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, Lemma C.3, p.37

import Mathlib
import Definitions.Def_ApproxGKR_SCAccepts
import Definitions.Def_ApproxGKR_E0

namespace ApproxGKR

open Classical in
/-- **Lemma C.3 (Approximate sum-check)** (p.37).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.3, Lemma C.3, p.37: "Let `f` have individual degree at most `D` in `nv ≥ 1`
variables. Suppose the initial claim differs from `Σ_{z∈H^{nv}} f(z)` by more than `t0`. For a
target terminal error `t_{nv} ≥ 0` and `0 < α < 1`, define `t_{j−1} = 7∆0 + h(tj + ∆0)/α`,
`j = nv, …, 1`. (C.13) Then sum-check, with the tolerance and arithmetic error specified above,
rejects or ends with error greater than `t_{nv}`, except with probability at most
`nvD(α^{1/D} + N^{−1})`."

For every adaptive prover and every verifier implementation with arithmetic error at most `∆₀`:
the number of challenge tuples `r ∈ (Fin N)^{nv}` on which sum-check accepts (degrees `≤ D`,
residuals `≤ 6∆₀`) and the final claim `Y_{nv}` is within `t_{nv}` of `f(r)` is at most
`N^{nv} · nv D(α^{1/D} + 1/N)`.

**Formalization Note** `H = Ω_h` for any `h ≥ 1`; `t₀ = scThr h α ∆₀ t_{nv} nv` is (C.13).
The lemma holds also for `D = 0` (then the bound is `0`), so `D ≥ 1` is not assumed. -/
theorem lemma_C_3 (nv N h D : ℕ) (f : MvPolynomial (Fin nv) ℂ) (Y0 : ℂ) (Δ₀ α tnv : ℝ)
    (P : SCProver nv N) (V : SCVerifier nv N)
    (hnv : 1 ≤ nv) (hN : 1 ≤ N) (hh : 1 ≤ h) (hf : ∀ v, f.degreeOf v ≤ D)
    (hΔ₀ : 0 ≤ Δ₀) (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 ≤ tnv)
    (hP : P.Adapted) (hV : V.Within P Y0 h Δ₀)
    (hinit : scThr (h : ℝ) α Δ₀ tnv nv <
      ‖Y0 - ∑ z : Fin nv → Fin h, MvPolynomial.eval (fun v => root h (z v).val) f‖) :
    ((Finset.univ.filter (fun r : Fin nv → Fin N =>
        SCAccepts P V D Δ₀ r ∧
          ‖scClaim Y0 V r nv - MvPolynomial.eval (fun v => root N (r v).val) f‖ ≤ tnv)).card : ℝ)
      ≤ (N : ℝ) ^ nv * (nv * D * (α ^ ((1 : ℝ) / D) + 1 / N)) := by sorry

end ApproxGKR
