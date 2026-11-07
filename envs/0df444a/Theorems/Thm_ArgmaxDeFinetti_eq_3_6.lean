-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_eq_3_6
-- name    : ArgmaxDeFinetti.eq_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:33.467231+00:00
-- url     : https://prove2.me/theorems/76a1c143-6fa2-4298-9f14-5262b6b8667a
-- title:
--   Eq. (3.6) — the argmax rounding object with $c=\langle u^{\otimes N},\psi\rangle>0$
-- statement:
--   Let $N\ge2$, $\mathcal H=\mathbb C^d$, and let $\psi\in\mathrm{Sym}^N(\mathcal H)$ be a unit vector. Then there is a unit vector
--   $$
--   u\in\arg\max_{\|v\|=1}\big|\langle v^{\otimes N},\psi\rangle\big|
--   $$
--   whose phase is adjusted so that
--   $$
--   c:=\langle u^{\otimes N},\psi\rangle>0 .
--   $$
--   The tensor power $u^{\otimes N}$ is the rounding object of the argmax principle, and $c$ is the overlap that Lemma 3.3 and Proposition 3.5 work with.
--
--   Differences from the source:
--   - encoding: c := ⟨u^⊗N, ψ⟩ > 0 → ∃ c : ℝ, 0 < c ∧ ⟨u^⊗N, ψ⟩ = c; reason: a complex number is > 0 exactly when it is a positive real
--   - encoding: H → ℂ^d; reason: a finite-dimensional complex Hilbert space in an orthonormal basis
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.2, p.23, eq. (3.6)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_IsSym

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **The argmax rounding object, eq. (3.6)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.2, p.23. For a unit vector `ψ ∈ Sym^N(H)` there is a
unit `u ∈ arg max_{∥v∥=1} |⟨v^{⊗N}, ψ⟩|` whose phase is adjusted so that `c := ⟨u^{⊗N}, ψ⟩ > 0`.

**Formalization Note** `H = ℂ^d`, norms Euclidean (`vnorm`), `⟨·,·⟩` conjugate-linear in the first argument
(`vinner`). `N ≥ 2` is the standing assumption of §3.1. "c > 0" is: the overlap is the real number `c` and `c > 0`. -/
theorem eq_3_6 (n d : ℕ) (hn : 2 ≤ n) (ψ : Vec n d) (hψ : IsSym ψ) (hψn : vnorm ψ = 1) :
    ∃ u : Fin d → ℂ, vnorm u = 1 ∧
      (∀ v : Fin d → ℂ, vnorm v = 1 → ‖vinner (tensorPow v n) ψ‖ ≤ ‖vinner (tensorPow u n) ψ‖) ∧
      ∃ c : ℝ, 0 < c ∧ vinner (tensorPow u n) ψ = c := by sorry

end ArgmaxDeFinetti
