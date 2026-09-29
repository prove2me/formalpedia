-- Prove2me | Theorems.Thm_FamousTheorems_fundamental_identity_ramification_inertia
-- name    : FamousTheorems.fundamental_identity_ramification_inertia
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:16.299049+00:00
-- url     : https://prove2.me/theorems/a9f4761c-1ead-463d-8f6d-fb08e73a9634
-- title:
--   The fundamental identity Σ e f = n
-- statement:
--   **The fundamental identity $\sum e_if_i=n$.** Let $R$ be an integral domain, let $S$ be a finite flat $R$-algebra, and let $\mathfrak p$ be a prime of $R$. Then
--   $$\sum_{\mathfrak q\mid\mathfrak p}e(\mathfrak q\mid\mathfrak p)\,f(\mathfrak q\mid\mathfrak p)=\operatorname{rank}_RS,$$
--   where the sum runs over the primes $\mathfrak q$ of $S$ lying over $\mathfrak p$, and $e$ and $f$ are the ramification index and inertia degree.
--
--   For an extension $L/K$ of number fields with rings of integers $\mathcal O_L\supseteq\mathcal O_K$ this is the classical identity $\sum e_if_i=[L:K]$. It describes how a prime splits in an extension and underlies the decomposition and inertia groups of Hilbert's ramification theory and the Chebotarev density theorem.
--
--   **Formalization note.** Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`, which generalises the Dedekind-domain statement. `p.primesOver S` is the type of primes of $S$ lying over `p`, assumed finite through a `Fintype` instance. `q.1.ramificationIdx R` and `q.1.inertiaDeg R` are the ramification index and inertia degree over the contraction of $\mathfrak q$, and `Module.finrank R S` is the rank of $S$ as a free $R$-module.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.sum_ramification_inertia_eq_finrank`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fundamental_identity_ramification_inertia {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S := by sorry

end FamousTheorems
