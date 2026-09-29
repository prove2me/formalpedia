-- Prove2me | Theorems.Thm_FamousTheorems_ionescu_tulcea_theorem
-- name    : FamousTheorems.ionescu_tulcea_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:00.678931+00:00
-- url     : https://prove2.me/theorems/61a21d31-fa96-4b76-bce9-c66664f9da87
-- title:
--   The Ionescu-Tulcea theorem
-- statement:
--   **The Ionescu-Tulcea theorem.** Let $(X_n)_{n\in\mathbb N}$ be measurable spaces and let $\kappa_n$ be Markov kernels from $X_0\times\dots\times X_n$ to $X_{n+1}$. Then for each starting time $a$ there is a kernel $\eta$ from $X_0\times\dots\times X_a$ to the infinite product $\prod_nX_n$ whose projection to the first $b+1$ coordinates is, for every $b$, the finite composition of the kernels $\kappa_a,\dots,\kappa_{b-1}$.
--
--   This theorem, due to Ionescu Tulcea (1949), constructs the law of a discrete-time stochastic process from its transition kernels. Unlike the Kolmogorov extension theorem it needs no topological assumptions on the state spaces. It is the foundation for Markov chains and Markov decision processes on general state spaces.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.Kernel.traj_map_frestrictLe`, with witness `Kernel.traj κ a`. `Preorder.frestrictLe b` restricts a sequence to coordinates `Finset.Iic b`. `Kernel.partialTraj κ a b` is the kernel obtained by composing $\kappa_a,\dots,\kappa_{b-1}$, which keeps the coordinates up to $a$ and samples the ones up to $b$ (or, for $b\le a$, simply forgets the later coordinates).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.Kernel.traj_map_frestrictLe`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ionescu_tulcea_theorem {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic n) → X i) (X (n + 1)))
    [∀ n, ProbabilityTheory.IsMarkovKernel (κ n)] (a : ℕ) :
    ∃ η : ProbabilityTheory.Kernel ((i : Finset.Iic a) → X i) ((n : ℕ) → X n),
      ∀ b : ℕ, η.map (Preorder.frestrictLe b) = ProbabilityTheory.Kernel.partialTraj κ a b := by sorry

end FamousTheorems
