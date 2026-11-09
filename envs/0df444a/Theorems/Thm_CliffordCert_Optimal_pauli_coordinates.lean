-- Prove2me | Theorems.Thm_CliffordCert_Optimal_pauli_coordinates
-- name    : CliffordCert.Optimal.pauli_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:49:05.690138+00:00
-- url     : https://prove2.me/theorems/1eee6677-d4c2-4e9f-b6b0-fb7dbd87b1bd
-- title:
--   Fact 3 — Pauli coordinates and orthonormality
-- statement:
--   For $n\ge1$ put $d=2^n$ and use the actual Hermitian Pauli matrices $P_v$ with binary commutation form $B$. Then
--   $$P_v^\dagger=P_v,\quad P_v^2=I_d,\quad P_vP_w=(-1)^{B(v,w)}P_wP_v,\quad\operatorname{Tr}(P_vP_w)=d\,1_{v=w}.$$
--   The matrices $P_v/\sqrt d$ form an orthonormal real basis of all Hermitian matrices. Every traceless Hermitian $T$ has a unique real expansion and energy identity
--   $$T=\frac1{\sqrt d}\sum_{v\ne0}t_vP_v,\qquad\|T\|_2^2=\sum_{v\ne0}t_v^2.$$
--   This fixes the coordinates and normalization used for universal compression.
--
--   Differences from the source:
--   - encoding: n-qubit matrices and labelled tensor registers → matrices indexed by Fin n → Fin 2 and tensor configurations indexed by finite functions; reason: these are the computational bases, with the first q qubits retained and the last n−q discarded
--   - encoding: real coefficients indexed by nonzero labels → a coefficient function on all labels with its zero-label coefficient fixed to zero; reason: this gives precisely the same unique coefficient vector
--   - encoding: field-valued binary labels and Clifford matrices → published signed Pauli and individual Clifford definitions with Fin 2 label and bundled-unitary adapters; reason: binary residues 0 and 1 preserve the Eq. (18) phase and tensor order; the Clifford predicate requires every list member, with no random weights
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 12, Fact 3, Eqs. (19)–(20) (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pauli_coordinates (n : ℕ) (hn : 1 ≤ n) :
    (∀ v : Label n, (pauli v).IsHermitian ∧ pauli v * pauli v = 1) ∧
    (∀ v w : Label n,
      pauli v * pauli w = ((-1 : ℂ)^(commutation v w).val) • (pauli w * pauli v)) ∧
    (∀ v w : Label n, Matrix.trace (pauli v * pauli w) =
      if v = w then (2 : ℂ)^n else 0) ∧
    (∀ v w : Label n, born
      (((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℂ) • pauli v)
      (((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℂ) • pauli w) = if v = w then 1 else 0) ∧
    (∀ T : Mat (Bits n), T.IsHermitian → ∃! t : Label n → ℝ,
      T = ∑ v, ((t v / Real.sqrt ((2 : ℝ)^n) : ℝ) : ℂ) • pauli v) ∧
    (∀ T : Mat (Bits n), T.IsHermitian → Matrix.trace T = 0 →
      ∃! t : Label n → ℝ, t 0 = 0 ∧
        T = ∑ v : Label n with v ≠ 0,
          ((t v / Real.sqrt ((2 : ℝ)^n) : ℝ) : ℂ) • pauli v ∧
        hsSq T = ∑ v : Label n with v ≠ 0, (t v)^2) := by sorry
end CliffordCert.Optimal
