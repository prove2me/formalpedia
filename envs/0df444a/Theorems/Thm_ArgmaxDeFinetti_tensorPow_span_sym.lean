-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_tensorPow_span_sym
-- name    : ArgmaxDeFinetti.tensorPow_span_sym
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:37.189381+00:00
-- url     : https://prove2.me/theorems/57da8a56-e87c-4a5f-bb88-44b05a4cf002
-- title:
--   §3.1.2 — tensor powers $u^{\otimes N}$ span $\mathrm{Sym}^N(\mathcal H)$
-- statement:
--   For $\mathcal H=\mathbb C^d$ and every $n$, a vector $\psi\in(\mathbb C^d)^{\otimes n}$ lies in the complex linear span of the tensor powers $\{u^{\otimes n}:u\in\mathbb C^d\}$ if and only if it is symmetric:
--   $$
--   \operatorname{span}_{\mathbb C}\{u^{\otimes n}:\ u\in\mathbb C^d\}=\mathrm{Sym}^n(\mathbb C^d).
--   $$
--   This is what makes the overlap $\max_{\|v\|=1}|\langle v^{\otimes N},\psi\rangle|$ positive for every nonzero symmetric $\psi$, so that the argmax rounding object exists.
--
--   Differences from the source:
--   - generalization: N from the standing context of §3.1 (N ≥ 2) → every n : ℕ; reason: the statement for all n specializes to N ≥ 2; the spanning statement holds for every n
--   - encoding: H → ℂ^d; reason: a finite-dimensional complex Hilbert space in an orthonormal basis
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.2, first sentence, p.23

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_IsSym

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **§3.1.2, first sentence**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.23: "The tensor-power vectors `{u^{⊗N} : u ∈ H}` span `Sym^N(H)`."

A vector `ψ ∈ (ℂ^d)^{⊗n}` lies in the complex span of `{u^{⊗n} : u ∈ ℂ^d}` if and only if it is symmetric.

**Formalization Note** `H = ℂ^d`; stated for every `n` and `d` (the paper's context has `N ≥ 2`). -/
theorem tensorPow_span_sym (n d : ℕ) (ψ : Vec n d) :
    ψ ∈ Submodule.span ℂ (Set.range (fun u : Fin d → ℂ => tensorPow u n)) ↔ IsSym ψ := by sorry

end ArgmaxDeFinetti
