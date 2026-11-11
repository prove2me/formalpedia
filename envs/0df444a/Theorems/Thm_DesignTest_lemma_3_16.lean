-- Prove2me | Theorems.Thm_DesignTest_lemma_3_16
-- name    : DesignTest.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:24.825901+00:00
-- url     : https://prove2.me/theorems/7a7b360d-b970-45e6-98a0-90ff7bdcacb3
-- title:
--   Lemma 3.16, eq. (21) — $F^{\mathrm{st}}_t(\nu)-1/D_{\mathrm{Sym}}=\|M_t(\nu)-M_t(\mathsf H)\|_2^2$
-- statement:
--   Let $d,t\ge1$ and let $\nu$ be any probability measure on pure states of $\mathbb C^d$. Then the $t$-th state frame potential exceeds its Haar value by exactly the squared Hilbert–Schmidt distance of the moment operators:
--   $$F^{\mathrm{st}}_t(\nu)-\frac1{D_{\mathrm{Sym}}}=\|M_t(\nu)-M_t(\mathsf H)\|_2^2 ,\qquad D_{\mathrm{Sym}}=\binom{d+t-1}{t}.$$
--
--   In particular $F^{\mathrm{st}}_t(\nu)\ge1/D_{\mathrm{Sym}}$ with equality exactly for exact state $t$-designs; this is the identity that turns design testing into estimating a single scalar, the frame potential.
--
--   **Formalization Note** $F^{\mathrm{st}}_t(\nu)=\mathrm{Re}\,\mathrm{Tr}[M_t(\nu)^2]$; $\mathsf H$ is `haarState d`.
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: F^st_t(ν) = Tr[M_t(ν)²] → framePotential ν t = Re Tr[M_t(ν)²]; reason: M_t(ν) is Hermitian, so the trace is real
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 3.16, eq. (21), p.20

import Mathlib
import Definitions.Def_DesignTest_momentDist

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Lemma 3.16, eq. (21)** (Frame-potential identity, state case). A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Lemma 3.16, eq. (21), p.20.

Let `d, t ≥ 1`. For any probability measure `ν` on pure states of `ℂ^d`,
`F^st_t(ν) − 1/D_Sym = ‖M_t(ν) − M_t(H)‖₂²`.

**Formalization Note.** `F^st_t(ν) = Re Tr[M_t(ν)²]` (`framePotential`), `H = haarState d`, `‖·‖₂` the
Hilbert–Schmidt norm, `D_Sym = C(d + t − 1, t)`. Only the state identity (21) is stated; (22)–(26) concern
unitary designs. -/
theorem lemma_3_16 (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) (ν : Measure (PureVec d))
    [IsProbabilityMeasure ν] :
    framePotential ν t - 1 / (DSym d t : ℝ) = hsNorm (moment ν t - moment (haarState d) t) ^ 2 := by sorry

end DesignTest
