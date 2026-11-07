-- Prove2me | Theorems.Thm_DiagLinesLDT_theorem_6_4
-- name    : DiagLinesLDT.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:31.094456+00:00
-- url     : https://prove2.me/theorems/899b0e7c-4ed7-40cf-bbf5-2508150c459f
-- title:
--   Theorem 6.4 — commutator obstruction to global consistency
-- statement:
--   Let $\{A^u\}_{u\in U}$ be projective measurements on $\mathcal H=\mathbb C^\iota$ with answers in a finite set, indexed by a finite set $U$. For every projective measurement $G=\{G_g\}_{g\in\Omega}$ on $\mathcal H$ whose outcomes $g$ evaluate to functions $U\to\mathrm{Ans}$,
--
--   $$\mathbb E_{u}\sum_{a}\sum_{g:\,g(u)=a}\langle\Phi|A^u_a\otimes G_g|\Phi\rangle\le 1-\frac{1}{32}\mathbb E_{u,v}\Gamma(u,v).$$
--
--   In the source, $U=\mathbb F_q^2$, the answers are $\mathbb F_q$, and $\Omega$ is the set of functions $\mathbb F_q^2\to\mathbb F_q$. In particular, this holds for every measurement whose outcomes are low-individual-degree polynomials.
--
--   Measurements that are far from commuting are far from any single measurement that determines all answers at once.
--
--   Differences from the source:
--   - generalization: U = 𝔽_q², answers 𝔽_q, H = ℂ^{𝔽_q³}, A the point measurements of the construction → any finite U, answer set and ι, any projective family A; reason: §7.1 applies the theorem in three settings as purely Hilbert-space algebra; it specializes to the printed statement
--   - generalization: outcomes are functions g : 𝔽_q² → 𝔽_q; in particular low-individual-degree polynomials → a finite outcome set Ω with an evaluation ev : Ω → U → Ans; reason: Ω = U → Ans with ev = id is the printed inequality, and Ω the polynomials with their evaluation is its "In particular"
--   - encoding: ⟨ψ|M ⊗ N|ψ⟩ → its real part; reason: for tensors of Hermitian operators the value is already real
--   - encoding: finite-dimensional Hilbert spaces and operators → ℂ^ι with matrices; reason: every finite-dimensional Hilbert space is one of these
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Theorem 6.4, p.19 ("purely Hilbert-space algebra", §7.1, p.22)

import Mathlib
import Definitions.Def_DiagLinesLDT_Gamma
import Definitions.Def_DiagLinesLDT_reducedAcc

namespace DiagLinesLDT

/-- Commutator obstruction to global consistency.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Theorem 6.4, p.19 ("purely Hilbert-space algebra", §7.1, p.22).

**Formalization Note** The source has `U = 𝔽_q²`, `Ans = 𝔽_q`, `ι = 𝔽_q³`, its point measurements as `A`,
and outcomes that are functions `g : U → Ans`. Here `A` is any projective family, and the outcome set `Ω`
carries an evaluation `ev`: `Ω = U → Ans` with `ev = id` is the printed inequality, and `Ω` the
low-individual-degree polynomials with `ev` their evaluation is its "In particular". -/
theorem theorem_6_4 {U Ans ι Ω : Type*} [Fintype U] [Fintype Ans] [DecidableEq Ans]
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (A : U → Ans → Matrix ι ι ℂ) (hA : ∀ u, MIPRE.IsPVM (A u))
    (ev : Ω → U → Ans) (G : Ω → Matrix ι ι ℂ) (hG : MIPRE.IsPVM G) :
    uniformAvg (fun u => ∑ a, ∑ g with ev g u = a, expect (maxEnt ι) (A u a) (G g)) ≤
      1 - (1 / 32) * uniformAvg (fun u => uniformAvg fun v => Gamma A u v) := by sorry

end DiagLinesLDT
